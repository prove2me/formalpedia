-- Prove2me | Theorems.Thm_MultiplayerNoCollision_theorem_1
-- name    : MultiplayerNoCollision.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:23:41.773525+00:00
-- url     : https://prove2.me/theorems/8b668ca8-254d-4d61-8427-701238681cd3
-- title:
--   Theorem 1 — a decentralized algorithm without collision information has expected regret $O(mK\log(T)/\Delta^2)$ (corrected: $\max\{1,\log T\}$ for $T=1$)
-- statement:
--   There is an absolute constant $C$ with the following property. For all numbers of players $m\ge2$, arms $K\ge m+1$ and rounds $T\ge1$ there is a policy $\pi$, a single rule used by every player that sees only her own arms, her own rewards and her private random seeds, such that for every reward model (rewards in $[0,1]$, reward vectors i.i.d. over rounds, independent of the players' i.i.d. uniform seeds) with means $\mu_1,\dots,\mu_K$, sorted means $\mu_{(1)}\ge\dots\ge\mu_{(K)}$ and gap $\Delta=\mu_{(m)}-\mu_{(m+1)}$,
--   $$\Delta^2\,\mathbb E[\mathrm{Regret}]\le C\,mK\max\{1,\log T\},$$
--   where $\mathrm{Regret}=T\sum_{k\le m}\mu_{(k)}-\sum_{t\in[T]}\sum_{j\in[m]}\mu_{A_j(t)}(1-C_{A_j(t)}(t))$ is the regret (2).
--
--   Equivalently, when $\Delta>0$, $\mathbb E[\mathrm{Regret}]=O(mK\log(T)/\Delta^2)$ for $T\ge2$. This was the first regret guarantee for multiplayer bandits in which a player cannot tell a collision from a zero reward.
--
--   Differences from the source:
--   - correction: O(mK log(T)/∆²), "for all admissible parameters" (T > 0 is admissible, p.3) → C mK max{1, log T}/∆²; reason: at T = 1 the printed bound is 0; with m = 2, K = 3, deterministic means (1, 1, 0) (∆ = 1), the two players use the same rule with independent seeds and empty histories, so they pull arm i with the same probability p_i and collide with probability Σp_i² ≥ 1/3, losing both rewards: E[Regret] ≥ 2/3 for every policy; for T ≥ 2, max{1, log T} ≤ log T/log 2
--   - encoding: K ≥ m (Assumption 1) → K ≥ m + 1; reason: ∆ = µ_m − µ_{m+1} and the stopping rule of Algorithm 1 need an (m+1)-th arm; only the undefined case K = m is excluded
--   - encoding: bound with ∆² in the denominator ("a vacuous bound if ∆ = 0", p.4) → ∆² · E[Regret] ≤ C mK max{1, log T}; reason: at ∆ = 0 the statement is the paper's vacuous bound; dividing by ∆ in Lean would give x/0 = 0 and a false claim
--   - reading: "there is an algorithm" (with no communication, own rewards only, the same algorithm for all players, knowledge of T and m, randomization; pp.3–4) → ∃ π : Policy K, chosen after m, K, T and before the probability space and the reward model; reason: these are the paper's standing constraints on algorithms; a larger class (collision feedback, player indices, knowledge of the means) would weaken the theorem
--   - encoding: means relabeled so that µ_1 ≥ ··· ≥ µ_K (p.3) → arbitrary mean vector; ∆ and the benchmark computed from the sorted means; reason: the relabeling is without loss of generality only because the players do not see labels; it is not imposed on the model
--   - generalization: the sequences {Y_{i,t}}_{t≥1} are i.i.d. (dependence between arms not stated) → the reward vectors (Y_{1,t}, …, Y_{K,t}) are i.i.d. over t; arbitrary dependence across arms within a round; reason: contains the model with all Y_{i,t} independent; the per-arm-only reading (e.g. Y_{2,t+1} = Y_{1,t}) breaks the independence of the current reward from the history that the proof uses on pp.9 and 12
--   - encoding: rounds t = 1, …, T, arms i ∈ [K], players j ∈ [m] → 0-based rounds t = 0, …, T − 1, arms Fin K, players Fin m; reason: indexing only; paper round t is Lean round t − 1
--   - encoding: "the strategy can randomize" (p.4) → player j uses in round t a private seed U_{j,t} uniform on [0,1]; all seeds are independent and independent of the rewards; reason: every randomized choice of the paper (a uniform arm, a uniform arm of G) is a measurable function of one uniform seed; the players do not communicate
--   - encoding: Y_{A_j(t),t} supported on [0,1]; random variables → Y_{i,t} measurable with 0 ≤ Y_{i,t} ≤ 1 at every outcome; reason: modification on a null set changes neither the law nor the play up to a null set
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, Theorem 1, p.4

import Mathlib
import Definitions.Def_MultiplayerNoCollision_GameModel
import Definitions.Def_MultiplayerNoCollision_kthLargest
import Definitions.Def_MultiplayerNoCollision_Policy
import Definitions.Def_MultiplayerNoCollision_profile

universe u

namespace MultiplayerNoCollision

open MeasureTheory ProbabilityTheory

/-- **Theorem 1 (logarithmic regret without collision information).**
Lugosi, Mehrabian, *Multiplayer bandits without observing collision information*,
arXiv:1808.08416v2, Theorem 1, p.4: "There is an algorithm with expected regret
`O(mK log(T)/∆²)`. In this theorem and throughout, the notation `f = O(g)` means there exists an
absolute constant `C` such that for all admissible parameters, `f ≤ Cg`."

There is an absolute constant `C` such that for all numbers of players `m ≥ 2`, arms `K ≥ m + 1`
and rounds `T ≥ 1` there is a policy `π` (one rule, used by every player, fed only her own arms,
her own rewards and her private seeds) such that for every probability space and every reward model
(rewards in `[0,1]`, reward vectors i.i.d. over rounds, independent of the players' i.i.d. uniform
seeds), with means `µ_i = E Y_{i,t}`, sorted means `µ_(1) ≥ ··· ≥ µ_(K)` and gap
`∆ = µ_(m) − µ_(m+1)`,
`∆² · E[Regret] ≤ C · m K · max{1, log T}`,
where `Regret = T ∑_{k ≤ m} µ_(k) − ∑_{t<T} ∑_j µ_{A_j(t)} (1 − C_{A_j(t)}(t))` is the regret (2).

**Formalization Note.** `C` is chosen before `m, K, T`, and the policy before the probability space
and the reward model (the policy may use `m, K, T`, Assumption 3, p.4, and nothing else). The
weak-feedback policy class is `Policy K`. The means are not assumed sorted; `∆` and the benchmark
are computed from the sorted means. The bound is multiplied by `∆²`, so `∆ = 0` gives the paper's
vacuous bound. `log T` is replaced by `max{1, log T}`: at `T = 1` the printed bound is `0`, which no
policy achieves. `K ≥ m + 1` because `∆ = µ_m − µ_{m+1}` needs an `(m+1)`-th arm. Rounds are 0-based
and arms are `Fin K`. -/
theorem theorem_1 : ∃ C : ℝ, ∀ m K T : ℕ, 2 ≤ m → m + 1 ≤ K → 1 ≤ T →
    ∃ π : Policy K, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Y : Fin K → ℕ → Ω → ℝ) (U : Fin m → ℕ → Ω → ℝ), GameModel P Y U →
        gap (means P Y) m ^ 2 * ∫ ω, regret π.act Y U (means P Y) T ω ∂P ≤
          C * m * K * max 1 (Real.log T) := by sorry

end MultiplayerNoCollision
