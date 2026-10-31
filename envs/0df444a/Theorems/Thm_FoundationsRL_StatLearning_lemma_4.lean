-- Prove2me | Theorems.Thm_FoundationsRL_StatLearning_lemma_4
-- name    : FoundationsRL.StatLearning.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:25.975226+00:00
-- url     : https://prove2.me/theorems/05625c66-b471-44d5-9527-567a4a2c823a
-- title:
--   Lemma 4 — Proposition 1, Part 1, in high probability
-- statement:
--   Let $\mathcal F$ be a finite class and assume $\ell\circ f\in[0,1]$ almost surely for every $f\in\mathcal F$. Then for $T\ge1$ and $\delta\in(0,1)$, with probability at least $1-\delta$ over the i.i.d. dataset, every empirical risk minimizer $\widehat f$ satisfies
--
--   $$
--   L(\widehat f)-\min_{f\in\mathcal F}L(f)\le2\sqrt{\frac{\log(2|\mathcal F|/\delta)}{2T}}.
--   $$
--
--   The in-expectation slow rate of Proposition 1 follows from this tail bound.
--
--   **Formalization Note** $L(\widehat f)$ is the population loss of the realized predictor, with the dataset held fixed.
--
--   Differences from the source:
--   - encoding: measurability left implicit → members of the class are measurable (ℓ ∘ f measurable); reason: the field's standing convention; the expectations are undefined otherwise
--   - encoding: with probability at least 1 − δ, δ unconstrained → 0 < δ < 1; reason: the range stated at (1.12)
--   - encoding: T not stated → T ≥ 1; reason: the bound divides by T
--   - encoding: f̂ ∈ argmin (1.6) → every measurable selection of the argmin; reason: the probability of the event is defined only for a measurable selection
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 4, p. 11

import Mathlib
import Definitions.Def_FoundationsRL_StatLearning_excessLoss
import Definitions.Def_FoundationsRL_StatLearning_dataLaw
import Definitions.Def_FoundationsRL_StatLearning_IsERM
open MeasureTheory

namespace FoundationsRL.StatLearning

/-- **Lemma 4** (Proposition 1, Part 1, high-probability form). Let `F` be finite and assume
`ℓ ∘ f ∈ [0, 1]` almost surely. Then with probability at least `1 − δ`, ERM satisfies
`L(f̂) − min_{f∈F} L(f) ≤ 2 √(log(2|F|/δ)/(2T))`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Lemma 4, p. 11.

**Formalization Note.** `excessLoss M ℓ F hF (fhat D)` is `L(f̂) − min_{f∈F} L(f)` by definition, and
`L(f̂)` is evaluated at the realized function, the dataset `D` being held fixed. Probability is over
`D ∼ (M⋆)^{⊗T}`. `ℓ ∘ f` is measurable, the field's standing convention. `δ ∈ (0, 1)` as at (1.12),
and `T ≥ 1` because the bound divides by `T`. -/
theorem lemma_4 {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (M : Measure (X × Y)) [IsProbabilityMeasure M] (ℓ : Y' → Y → ℝ)
    (F : Finset (X → Y')) (hF : F.Nonempty)
    (hmeas : ∀ f ∈ F, Measurable fun z : X × Y => ℓ (f z.1) z.2)
    (hbdd : ∀ f ∈ F, ∀ᵐ z ∂M, ℓ (f z.1) z.2 ∈ Set.Icc (0 : ℝ) 1)
    (T : ℕ) (hT : 0 < T) (fhat : (Fin T → X × Y) → X → Y') (hfhat : IsERM ℓ F fhat)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (dataLaw M T).real {D | excessLoss M ℓ F hF (fhat D) ≤
      2 * Real.sqrt (Real.log (2 * (F.card : ℝ) / δ) / (2 * (T : ℝ)))} := by sorry

end FoundationsRL.StatLearning
