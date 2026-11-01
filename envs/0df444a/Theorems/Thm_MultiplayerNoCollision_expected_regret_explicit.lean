-- Prove2me | Theorems.Thm_MultiplayerNoCollision_expected_regret_explicit
-- name    : MultiplayerNoCollision.expected_regret_explicit
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:28.825325+00:00
-- url     : https://prove2.me/theorems/a6f32de2-75ec-4c9f-ad95-af6b7f391625
-- title:
--   Proof of Theorem 1, p.13 — $\mathbb E[\mathrm{Regret}]\le m\min\{T,\lceil 625g/\Delta^2+4m\log(m^2T)/\Delta\rceil\}+2$
-- statement:
--   All $m\ge2$ players run Algorithm 1 for $T\ge1$ rounds, with $K\ge m+1$ arms and rewards and seeds as in the model. Let $\Delta=\mu_{(m)}-\mu_{(m+1)}>0$, $g=128K\log(3Km^2T^2)$ and $X=625g/\Delta^2+4m\log(m^2T)/\Delta$. Then
--   $$\mathbb E[\mathrm{Regret}]\le m\cdot\min\{T,\lceil X\rceil\}+2.$$
--
--   The first term is the regret of the rounds before $X$, at most $m$ per round, and the $+2$ is the regret $mT$ on the event of probability $2/(mT)$ where Lemma 6 or Lemma 7 fails. The page writes the first term as $O(mK\log(KT)/\Delta^2)$.
--
--   Differences from the source:
--   - reading: O(mK log(KT)/∆²) + 2 → m · min{T, ⌈625g/∆² + 4m log(m²T)/∆⌉} + 2; reason: the proof's explicit count: at most m regret in each of the rounds t < X of the T rounds; the O-form follows from it (see the companion log(KT) → log T item)
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

/-- **Proof of Theorem 1: the expected regret of Algorithm 1.**
Lugosi, Mehrabian, *Multiplayer bandits without observing collision information*,
arXiv:1808.08416v2, proof of Theorem 1, p.13: "During each round, the regret is at most `m`, hence
the total regret incurred during the first three phases is bounded by `O(mK log(KT)/∆²)` and the
regret afterwards would be `0`. On the other hand, with the remaining `2/mT` probability, the regret
is at most `mT`. Therefore, the expected regret is at most `O(mK log(KT)/∆²) + 2`, as required."

All `m` players run Algorithm 1 for `T` rounds, `∆ = µ_m − µ_{m+1} > 0` and
`g = 128 K log(3 K m² T²)`. With `X = 625g/∆² + 4m log(m²T)/∆`,
`E[Regret] ≤ m · min{T, ⌈X⌉} + 2`.

**Formalization Note.** The page's `O(mK log(KT)/∆²)` is the regret of the rounds before `X`, at
most `m` per round; it is stated with the explicit quantity `m · min{T, ⌈X⌉}` of the proof
(`⌈X⌉` counts the 0-based rounds `t < X`). The expected regret is the integral of `regret`
(the regret (2) with the true means `µ_i = E Y_{i,0}`). -/
theorem expected_regret_explicit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (m K T : ℕ) [NeZero K] (hm : 2 ≤ m) (hK : m + 1 ≤ K) (hT : 1 ≤ T)
    (Y : Fin K → ℕ → Ω → ℝ) (U : Fin m → ℕ → Ω → ℝ) (hmodel : GameModel P Y U)
    (hΔ : 0 < gap (means P Y) m) :
    ∫ ω, regret (algorithm1 m K T) Y U (means P Y) T ω ∂P ≤
      (m : ℝ) * ((min T ⌈625 * gParam m K T / gap (means P Y) m ^ 2 +
        4 * m * Real.log ((m : ℝ) ^ 2 * T) / gap (means P Y) m⌉₊ : ℕ) : ℝ) + 2 := by sorry

end MultiplayerNoCollision
