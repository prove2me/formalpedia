-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_toAmbientL2_toIntrinsicL2_408915f
-- name    : FunctionalInequalities.Energy.Euclidean.toAmbientL2_toIntrinsicL2_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:56.571859+00:00
-- url     : https://prove2.me/theorems/4f7e18d8-b7b8-4c49-a7af-4e885e476e35
-- title:
--   Ambient Reconstruction After Intrinsic Coordinates
-- statement:
--   This is an identity for the ambient and intrinsic $L^2$ coordinate maps.
--
--   Let $E$ be a finite-dimensional real inner-product normed space with its Borel measurable structure and second-countable topology, and let $\mu$ be a probability measure on $E$. For every element $f$ of $L^2(\mu)$, first map $f$ to intrinsic coordinates using `toIntrinsicL2`, and then map it back to ambient coordinates using `toAmbientL2`. The result is exactly $f$:
--
--   $$
--   \operatorname{toAmbientL2}(\mu)\bigl(\operatorname{toIntrinsicL2}(\mu)(f)\bigr)=f.
--   $$
--
--   The declaration is `toAmbientL2_toIntrinsicL2`. No completeness assumption on $E$ is required by the declaration, and the equality is equality in the $L^2$ subtype rather than merely pointwise equality of representatives. This provides the retraction identity needed when comparing ambient and intrinsic energies.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Basic.lean#L46-L74 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic`, declaration `FunctionalInequalities.Energy.Euclidean.toAmbientL2_toIntrinsicL2`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
omit [CompleteSpace E]

@[simp]
theorem FunctionalInequalities.Energy.Euclidean.toAmbientL2_toIntrinsicL2_408915f (μ : ProbabilityMeasure E)
    (f : Lp ℝ 2 (μ : Measure E)) :
    toAmbientL2 μ (toIntrinsicL2 μ f) = f := by sorry
