-- Prove2me | Theorems.Thm_MultiplayerNoCollision_occupation_whp
-- name    : MultiplayerNoCollision.occupation_whp
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:49.611086+00:00
-- url     : https://prove2.me/theorems/bc51c1f3-3e16-41fb-9c88-74b801840865
-- title:
--   Proof of Theorem 1, p.13 — w.p. $\ge1-2/mT$, after $625g/\Delta^2+4m\log(m^2T)/\Delta$ rounds the players sit on distinct best arms
-- statement:
--   All $m\ge2$ players run Algorithm 1 for $T\ge1$ rounds, with $K\ge m+1$ arms and rewards and seeds as in the model. Let $\Delta=\mu_{(m)}-\mu_{(m+1)}>0$, $g=128K\log(3Km^2T^2)$ and
--   $$X=\frac{625g}{\Delta^2}+\frac{4m\log(m^2T)}{\Delta}.$$
--   With probability at least $1-2/(mT)$, in every round $t<T$ with $t\ge X$ the players pull pairwise distinct arms, each one of the $m$ arms with the largest means.
--
--   From round $X$ on, the players therefore collect exactly the benchmark $\sum_{k\le m}\mu_{(k)}$ and incur no regret.
--
--   Differences from the source:
--   - reading: O(K log(KT)/∆²) many rounds → the explicit quantity X = 625g/∆² + 4m log(m²T)/∆ of the same sentence; reason: the O-form is a consequence of the explicit one
--   - encoding: "after at most X many rounds" the first three phases are finished → every 0-based round t < T with t ≥ X; reason: if Phases 1–3 occupy R ≤ X rounds, 0-based rounds t ≥ R are in Phase 4
--   - reading: 2/mT → 2/(mT); reason: sum of the failure probabilities 1/(mT) of Lemmas 6 and 7
--   - encoding: K ≥ m (Assumption 1) → K ≥ m + 1; reason: ∆ = µ_m − µ_{m+1} and the stopping rule of Algorithm 1 need an (m+1)-th arm; only the undefined case K = m is excluded
--   - encoding: bounds with ∆ in a denominator → hypothesis ∆ > 0; reason: the bounds divide by ∆; only the undefined case ∆ = 0 is excluded
--   - encoding: Algorithm 1 with MusicalChairs1 (p.10), state µ̂, τ, Best-m-arms, occupied arm → algorithm1: a rule of (round, own history, own seed); uniform arm = ⌊K u⌋ clamped, uniform arm of G = the ⌊|G| u⌋-th element of G in increasing order (clamped); reason: every state variable of Algorithm 1 is a deterministic function of the own history; the seed maps push the uniform law to the uniform law on [K] and on G
--   - encoding: rounds t = 1, …, T, arms i ∈ [K], players j ∈ [m] → 0-based rounds t = 0, …, T − 1, arms Fin K, players Fin m; reason: indexing only; paper round t is Lean round t − 1
--   - encoding: "the strategy can randomize" (p.4) → player j uses in round t a private seed U_{j,t} uniform on [0,1]; all seeds are independent and independent of the rewards; reason: every randomized choice of the paper (a uniform arm, a uniform arm of G) is a measurable function of one uniform seed; the players do not communicate
--   - generalization: the sequences {Y_{i,t}}_{t≥1} are i.i.d. (dependence between arms not stated) → the reward vectors (Y_{1,t}, …, Y_{K,t}) are i.i.d. over t; arbitrary dependence across arms within a round; reason: contains the model with all Y_{i,t} independent; the per-arm-only reading (e.g. Y_{2,t+1} = Y_{1,t}) breaks the independence of the current reward from the history that the proof uses on pp.9 and 12
--   - encoding: Y_{A_j(t),t} supported on [0,1]; random variables → Y_{i,t} measurable with 0 ≤ Y_{i,t} ≤ 1 at every outcome; reason: modification on a null set changes neither the law nor the play up to a null set
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, proof of Theorem 1, p.13

import Mathlib
import Definitions.Def_MultiplayerNoCollision_GameModel
import Definitions.Def_MultiplayerNoCollision_kthLargest
import Definitions.Def_MultiplayerNoCollision_profile
import Definitions.Def_MultiplayerNoCollision_algorithm1

namespace MultiplayerNoCollision

open MeasureTheory ProbabilityTheory

/-- **Proof of Theorem 1: after `625g/∆² + 4m log(m²T)/∆` rounds the players sit on distinct best
arms, with probability at least `1 − 2/mT`.**
Lugosi, Mehrabian, *Multiplayer bandits without observing collision information*,
arXiv:1808.08416v2, proof of Theorem 1, p.13: "By Lemma 6 and Lemma 7, with probability at least
`1 − 2/mT`, the first three phases finish for all players after at most
`625g/∆² + 4m log(m²T)/∆ = O(K log(KT)/∆²)` many rounds. After this time, each player has occupied
one of the best `m` arms and different players have occupied distinct arms."

All `m` players run Algorithm 1 for `T` rounds, `∆ = µ_m − µ_{m+1} > 0` and
`g = 128 K log(3 K m² T²)`. With probability at least `1 − 2/(mT)`, in every round
`t ∈ {0, …, T − 1}` with `t ≥ 625g/∆² + 4m log(m²T)/∆`, the players pull pairwise distinct arms and
each of them pulls one of the `m` arms with the largest means.

**Formalization Note.** Rounds are 0-based: when at most `X` rounds have passed in Phases 1–3, every
0-based round `t ≥ X` is in Phase 4. The `O(K log(KT)/∆²)` of the page is not stated; the explicit
quantity is. `2/mT` is `2/(mT)`. -/
theorem occupation_whp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m K T : ℕ) [NeZero K] (hm : 2 ≤ m) (hK : m + 1 ≤ K) (hT : 1 ≤ T)
    (Y : Fin K → ℕ → Ω → ℝ) (U : Fin m → ℕ → Ω → ℝ) (hmodel : GameModel P Y U)
    (hΔ : 0 < gap (means P Y) m) :
    1 - 2 / ((m : ℝ) * T) ≤ P.real {ω | ∀ t : ℕ, t < T →
      625 * gParam m K T / gap (means P Y) m ^ 2 +
          4 * m * Real.log ((m : ℝ) ^ 2 * T) / gap (means P Y) m ≤ (t : ℝ) →
        (∀ j j' : Fin m, j ≠ j' →
          profile (algorithm1 m K T) Y U ω t j ≠ profile (algorithm1 m K T) Y U ω t j') ∧
        ∀ j : Fin m, profile (algorithm1 m K T) Y U ω t j ∈ topSet (means P Y) m} := by sorry

end MultiplayerNoCollision
