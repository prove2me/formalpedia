-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_expTilt_tilted_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.expTilt_tilted_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:03:42.150338+00:00
-- url     : https://prove2.me/theorems/1823b60a-9b2c-4864-be50-135452ad15fd
-- title:
--   Composition Rule for Exponential Tilts
-- statement:
--   This theorem relates an exponential tilt of a tilted measure to a single tilt with a modified potential.
--
--   Let $E$ be a real inner-product space, let $m$ be a measure on $E$, and let $V:E\to\mathbb R$. Assume that $x\mapsto e^{-V(x)}$ is integrable with respect to $m$. For every $z\in E$,
--
--   $$\operatorname{expTilt}\bigl(m.\operatorname{tilted}(-V)\bigr)(z)
--   =m.\operatorname{tilted}\bigl(-(V-\langle z,\cdot\rangle)\bigr).$$
--
--   The definitions `expTilt` and `Measure.tilted` are used exactly as stated; no finite-dimensional, completeness, Borel, or Haar-measure assumptions are required by the theorem. This identity is a basic algebraic rule for manipulating exponential tilts.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean#L89-L104 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.expTilt_tilted`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : Measure E) [m.IsAddHaarMeasure]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.expTilt_tilted_408915f {V : E → ℝ} (hV : Integrable (fun x => Real.exp ((-V) x)) m) (z : E) :
    expTilt (m.tilted (-V)) z = m.tilted (-fun y => V y - ⟪z, y⟫) := by sorry
