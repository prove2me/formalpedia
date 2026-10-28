-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_integral_affineSubtract_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.integral_affineSubtract_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:45.118231+00:00
-- url     : https://prove2.me/theorems/b464f0e5-346a-4249-bc07-ab1613a70aef
-- title:
--   Integral Formula for Affine Subtraction
-- statement:
--   This gives the exact integral correction under affine subtraction.
--
--   Let $\mu$ be a finite measure, let $f:E\to\overline{\mathbb R}$ be potential-integrable, let $a\in E$, and let $b\in\mathbb R$. Assume the identity map is integrable with respect to $\mu$. Then
--
--   $$
--   \int \operatorname{toReal}\bigl((\operatorname{affineSubtract} f\ a\ b)(x)\bigr)\,d\mu
--   =
--   \int \operatorname{toReal}(f(x))\,d\mu
--   -\int\langle a,x\rangle\,d\mu
--   -(\mu(E)).\operatorname{toReal}\,b.
--   $$
--
--   The total mass factor is retained; invariance under constant shifts is therefore not asserted for arbitrary finite measures.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_affineSubtract
--       (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
--       (hfirst : Integrable (fun x : E => x) μ) :
--       (∫ x, (affineSubtract f a b x).toReal ∂μ) =
--         (∫ x, (f x).toReal ∂μ) - (∫ x, inner ℝ a x ∂μ) - (μ Set.univ).toReal * b
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Affine`](https://prove2.me/theorems/763df6ce-b81b-47cb-8b6b-d4d0c79b4571).
--
--   Definition modules: [`Analysis/Convex/Affine`](https://prove2.me/theorems/ba0d4420-d959-4afc-bf5b-05caa7b55a1c), [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c).
--
--   Previous: [`affineSubtract_potentialIntegrable`](https://prove2.me/theorems/f9035aa8-a93c-47ed-80fb-13efe5d1963a).
--
--   [Source excerpt, lines 95–99](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Affine.lean#L95-L99) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Affine.lean#L92-L112 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Affine`, declaration `FunctionalInequalities.Probability.MomentMeasure.integral_affineSubtract`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Affine

open FunctionalInequalities.Analysis
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E}
variable [MeasureTheory.IsFiniteMeasure μ]
omit [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.integral_affineSubtract_readable
    (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) :
    (∫ x, (affineSubtract f a b x).toReal ∂μ) =
      (∫ x, (f x).toReal ∂μ) - (∫ x, inner ℝ a x ∂μ) - (μ Set.univ).toReal * b := by sorry
