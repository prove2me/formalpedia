-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_affineSupport_translateLaw_408915f
-- name    : FunctionalInequalities.Probability.affineSupport_translateLaw_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:29:35.785982+00:00
-- url     : https://prove2.me/theorems/0b7acd27-16d5-4464-b634-74dab6463f52
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/IntrinsicTranslation.lean#L29-L49 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.IntrinsicTranslation`, declaration `FunctionalInequalities.Probability.affineSupport_translateLaw`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_IntrinsicTranslation
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section
open MeasureTheory Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
variable (μ : ProbabilityMeasure E) (b : E)

theorem FunctionalInequalities.Probability.affineSupport_translateLaw_408915f :
    affineSupport (translateLaw μ b) =
      (affineSupport μ).map (AffineEquiv.constVAdd ℝ E b).toAffineMap := by sorry
