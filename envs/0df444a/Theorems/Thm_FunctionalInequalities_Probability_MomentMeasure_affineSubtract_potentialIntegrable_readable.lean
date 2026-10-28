-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_affineSubtract_potentialIntegrable_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.affineSubtract_potentialIntegrable_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:52.091981+00:00
-- url     : https://prove2.me/theorems/f9035aa8-a93c-47ed-80fb-13efe5d1963a
-- title:
--   Integrability Under Affine Subtraction
-- statement:
--   This states that affine subtraction preserves potential integrability under a first-moment hypothesis.
--
--   Let $\mu$ be a finite measure on a real inner-product space, let $f:E\to\overline{\mathbb R}$ be potential-integrable with respect to $\mu$, and let $a\in E$, $b\in\mathbb R$. Assume the identity map is integrable:
--
--   $$
--   \int\|x\|\,d\mu(x)<\infty.
--   $$
--
--   Then `affineSubtract f a b` is also potential-integrable with respect to $\mu$. No Borel-space instance is required by the statement, and no supporting affine plane is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem affineSubtract_potentialIntegrable
--       (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
--       (hfirst : Integrable (fun x : E => x) μ) :
--       PotentialIntegrable (affineSubtract f a b) μ
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Affine`](https://prove2.me/theorems/763df6ce-b81b-47cb-8b6b-d4d0c79b4571).
--
--   Definition modules: [`Analysis/Convex/Affine`](https://prove2.me/theorems/ba0d4420-d959-4afc-bf5b-05caa7b55a1c), [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c).
--
--   Next: [`integral_affineSubtract`](https://prove2.me/theorems/b464f0e5-346a-4249-bc07-ab1613a70aef).
--
--   [Source excerpt, lines 70–73](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Affine.lean#L70-L73) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Affine.lean#L67-L91 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Affine`, declaration `FunctionalInequalities.Probability.MomentMeasure.affineSubtract_potentialIntegrable`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Affine

open FunctionalInequalities.Analysis
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E}
variable [MeasureTheory.IsFiniteMeasure μ]
omit [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.affineSubtract_potentialIntegrable_readable
    (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) :
    PotentialIntegrable (affineSubtract f a b) μ := by sorry
