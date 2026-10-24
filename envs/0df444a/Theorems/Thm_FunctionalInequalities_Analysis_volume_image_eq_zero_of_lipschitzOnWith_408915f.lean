-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_volume_image_eq_zero_of_lipschitzOnWith_408915f
-- name    : FunctionalInequalities.Analysis.volume_image_eq_zero_of_lipschitzOnWith_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:10:58.207659+00:00
-- url     : https://prove2.me/theorems/2538b617-bb35-4961-9a27-76cd74333859
-- title:
--   Lipschitz Images of Lebesgue Null Sets
-- statement:
--   This is an equidimensional measure-theoretic lemma.
--
--   Let $E$ be a finite-dimensional real inner-product space equipped with its measurable and Borel structures. Let $f:E\to E$, let $K\in[0,\infty)$ (`NNReal`), and let $s\subseteq E$. Assume:
--
--   1. $f$ is Lipschitz on $s$ with constant $K$.
--   2. The Lebesgue measure of $s$ is zero:
--      $$\operatorname{vol}(s)=0.$$
--
--   Then the image is also Lebesgue-null:
--
--   $$\operatorname{vol}(f(s))=0.$$
--
--   The declaration `volume_image_eq_zero_of_lipschitzOnWith` does not require measurability of $s$ as an explicit hypothesis. It is restricted to maps from a finite-dimensional space to itself.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Sard/Equidimensional.lean#L129-L147 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Sard.Equidimensional`, declaration `FunctionalInequalities.Analysis.volume_image_eq_zero_of_lipschitzOnWith`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section
open MeasureTheory Module Set
open scoped ENNReal NNReal RealInnerProductSpace
section LT12D1LipschitzNullImage
open MeasureTheory Set
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.volume_image_eq_zero_of_lipschitzOnWith_408915f {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {K : NNReal} {s : Set E} (hf : LipschitzOnWith K f s)
    (hs : (volume : Measure E) s = 0) : (volume : Measure E) (f '' s) = 0 := by sorry
