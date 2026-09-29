-- Prove2me | Theorems.Thm_OnlineConvexOpt_LearningTheory_oco_to_pac_generalization
-- name    : OnlineConvexOpt.LearningTheory.oco_to_pac_generalization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T20:47:25.611854+00:00
-- url     : https://prove2.me/theorems/ee5478aa-2f5c-4f5b-9ba8-145882a4eb83
-- title:
--   Theorem 9.5 — OCO regret implies PAC generalization (goal)
-- statement:
--   **Statement (Theorem 9.5, p. 158, PDF p. 180).** Let $A$ be an OCO algorithm whose regret
--   after $T$ iterations is guaranteed to be bounded by $\mathrm{Regret}_T(A)$. Then for any
--   $\delta > 0$, with probability at least $1-\delta$,
--   $$\mathrm{error}(\bar h) \le \mathrm{error}(h^\star) + \frac{\mathrm{Regret}_T(A)}{T} +
--   \sqrt{\frac{8\log(2/\delta)}{T}}.$$
--
--   This is the chapter's payoff: any sublinear-regret OCO algorithm, run via Algorithm 29's
--   reduction on i.i.d. labeled examples, is automatically an agnostic PAC learning algorithm —
--   a single regret-minimization technique yields a generalization guarantee for every
--   hypothesis class with a low-regret OCO algorithm, including the infinite (convex) classes
--   the book's finite-class Theorem 9.4 does not cover.
--
--   **Formalization Note.** $\bar h$ is Algorithm 29's output (`IsAgnosticReductionRun`),
--   $h^\star = \arg\min_{h\in H}\{\mathrm{error}(h)\}$. $A$'s regret guarantee (`hA`) is stated
--   using the published `OnlineConvexOpt.FirstOrder.RegretT` (Chunk 03, reused as a `kind:
--   reference` item) as a property of $A$ holding for every cost sequence and horizon — "an
--   algorithm whose regret is guaranteed to be bounded by `Regret_T(A)`" — not a one-off fact
--   about the realized random cost sequence. `hAnonant`, also reusing published prior art
--   (`OnlineConvexOpt.FirstOrder.IsOnlineAlgorithm`), requires $A$ to be non-anticipating and to
--   play inside $H$: `hA`'s universal regret guarantee, quantified over an arbitrary cost
--   sequence, says nothing on its own about the specific plays `IsAgnosticReductionRun`'s `h`
--   produces from truncated cost sequences unless `A`'s decision at each round is known not to
--   depend on cost functions from later rounds — exactly what `hAnonant` supplies, and what a
--   moderator change request (2026-09-19) caught was missing from the first draft. Measurability
--   hypotheses `hpred`, `hℓmeas` (each of `pred`, `ℓ` measurable as an uncurried function) and
--   `hhbar` (the reduction's output measurable) guard `GeneralizationError`'s integral and the
--   final probability event `{ω | ...}` against Mathlib's junk-zero fallback on a non-measurable
--   input, which would otherwise let the theorem hold trivially regardless of the regret bound.
--
--   The loss `ℓ` is assumed bounded in `[0,1]` (`hℓbdd`), the
--   book's implicit standing assumption for the concentration argument (matching the zero-one
--   loss and the bounded hinge-loss examples §9.1.3 gives); this is not stated in Theorem 9.5's
--   own display but is required for the `√(8log(2/δ)/T)` term's derivation via Azuma's
--   inequality (§9.2.1) — see `MODERATION_NOTES.md`. The optional corollary form
--   ("`T = O((1/ε²)log(1/δ) + T_ε(A))` implies `error(h̄) ≤ error(h*) + ε`") is not drafted, per
--   `BRIEF.md`'s "otherwise keep the milestone to the displayed inequality."
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 158, Theorem 9.5 (PDF p. 180)

import Mathlib
import Definitions.Def_OnlineConvexOpt_LearningTheory_GeneralizationError
import Definitions.Def_OnlineConvexOpt_LearningTheory_AgnosticReduction
import Definitions.Def_OnlineConvexOpt_FirstOrder_Algorithm
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open MeasureTheory

namespace OnlineConvexOpt.LearningTheory

/-- Theorem 9.5 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 158, PDF p. 180). Let `A` be an OCO algorithm whose regret after `T`
iterations is guaranteed to be bounded by `RegretT(A)`. Then for any `δ > 0`, with probability
at least `1 − δ`, it holds that
`error(h̄) ≤ error(h⋆) + Regret_T(A)/T + √(8 log(2/δ)/T)`.

`h̄` is Algorithm 29's output (`IsAgnosticReductionRun`), `h⋆ = arg min_{h∈H}{error(h)}`
(p. 158). `A`'s regret guarantee is stated as `hA`, reusing the published
`OnlineConvexOpt.FirstOrder.RegretT` (Chunk 03): for every cost sequence and every horizon, `A`'s
regret against the best fixed hypothesis in `H` is at most `RegretBoundA T` — the hypothesis "an
OCO algorithm whose regret is guaranteed to be bounded by `RegretT(A)`" made explicit as a
property of `A` (not a one-off fact about the realized random cost sequence). `hAnonant`, reusing
the published `OnlineConvexOpt.FirstOrder.IsOnlineAlgorithm` (Chunk 03), requires `A` to be
non-anticipating and to play inside `H`: without it, `hA`'s universal regret guarantee over an
arbitrary cost sequence says nothing about the specific plays `IsAgnosticReductionRun`'s `h`
produces from truncated cost sequences, since those truncations agree with the real realized
sequence only on rounds strictly before the one being played. Measurability hypotheses
(`hpred`, `hℓmeas`, `hhbar`) guard `GeneralizationError`'s integral and the final probability
event against silently collapsing to Mathlib's junk value on a non-measurable input. -/
theorem oco_to_pac_generalization
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (H : Set E) (pred : E → X → ℝ) (ℓ : ℝ → Y → ℝ)
    (hℓbdd : ∀ yhat y, 0 ≤ ℓ yhat y ∧ ℓ yhat y ≤ 1)
    (hpred : Measurable (Function.uncurry pred))
    (hℓmeas : Measurable (Function.uncurry ℓ))
    (A : (ℕ → E → ℝ) → ℕ → E)
    (hAnonant : OnlineConvexOpt.FirstOrder.IsOnlineAlgorithm H A)
    (RegretBoundA : ℕ → ℝ)
    (hA : ∀ (T : ℕ) (f : ℕ → E → ℝ), 1 ≤ T →
      OnlineConvexOpt.FirstOrder.RegretT H f (A f) T ≤ RegretBoundA T)
    (T : ℕ) (hT : 1 ≤ T)
    (samp : ℕ → Ω → X × Y) (h : ℕ → Ω → E) (hbar : Ω → E)
    (hrun : IsAgnosticReductionRun Prob D pred ℓ A T samp h hbar)
    (hhbar : Measurable hbar)
    (hstar : E) (hstar_mem : hstar ∈ H)
    (hstar_min : ∀ y ∈ H, GeneralizationError D pred ℓ hstar ≤ GeneralizationError D pred ℓ y)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ) ≤
      (Prob {ω | GeneralizationError D pred ℓ (hbar ω) ≤
        GeneralizationError D pred ℓ hstar + RegretBoundA T / T +
          Real.sqrt (8 * Real.log (2 / δ) / T)}).toReal := by sorry

end OnlineConvexOpt.LearningTheory
