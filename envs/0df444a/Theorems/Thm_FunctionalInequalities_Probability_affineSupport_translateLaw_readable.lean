-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_affineSupport_translateLaw_readable
-- name    : FunctionalInequalities.Probability.affineSupport_translateLaw_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:44.798296+00:00
-- url     : https://prove2.me/theorems/618c4d8e-695f-405d-a488-6790e221d360
-- title:
--   Affine Support Under Translation
-- statement:
--   This is the affine-support transport identity for translated probability laws.
--
--   Let $E$ be a finite-dimensional real inner-product normed space with Borel and second-countable structure. Let $\mu$ be a probability measure on $E$ and let $b\in E$. If `translateLaw μ b` is the pushforward of $\mu$ by $x\mapsto b+x$, then
--
--   $$\operatorname{affineSupport}(\operatorname{translateLaw}(\mu,b))
--   =\bigl(\operatorname{affineSupport}(\mu)\bigr)+b.$$
--
--   The right side is expressed in Lean as the affine-subspace map under `AffineEquiv.constVAdd`. This is a geometric support-transport lemma.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem affineSupport_translateLaw :
--       affineSupport (translateLaw μ b) =
--         (affineSupport μ).map (AffineEquiv.constVAdd ℝ E b).toAffineMap
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/IntrinsicTranslation`](https://prove2.me/theorems/b9ce8338-e7be-450b-86d4-c0e89470d643).
--
--   Definition modules: [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81), [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564).
--
--   [Source excerpt, lines 30–32](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/IntrinsicTranslation.lean#L30-L32) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/IntrinsicTranslation.lean#L29-L49 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.IntrinsicTranslation`, declaration `FunctionalInequalities.Probability.affineSupport_translateLaw`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_IntrinsicTranslation

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
variable (μ : MeasureTheory.ProbabilityMeasure E) (b : E)

theorem FunctionalInequalities.Probability.affineSupport_translateLaw_readable :
    affineSupport (translateLaw μ b) =
      (affineSupport μ).map (AffineEquiv.constVAdd ℝ E b).toAffineMap := by sorry
