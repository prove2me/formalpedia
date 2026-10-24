-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_sum_selected_eq_408915f
-- name    : FunctionalInequalities.KLS.BKL.sum_selected_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:16:39.792549+00:00
-- url     : https://prove2.me/theorems/7a5056dd-0642-4c97-bbfb-5ed7cc97b63b
-- title:
--   Reindexing a Mask-Selected Finite Sum
-- statement:
--   This reindexes a sum over Boolean masks by the selected and complementary slots.
--
--   Let $w:\iota\to E$, let $q:\operatorname{Fin}(k)\to\{\mathrm{false},\mathrm{true}\}$, and let $G$ map pairs of lists in $E$ to $\mathbb{R}$. If the mask has $c_1$ true entries and its complement has $c_2$ true entries, then
--
--   $$
--   \sum_{J:\operatorname{Fin}(k)\to\iota}
--   G\bigl(w(J)\text{ selected by }q,\,w(J)\text{ selected by }\neg q\bigr)
--   =
--   \sum_{J_1:\operatorname{Fin}(c_1)\to\iota}
--   \sum_{J_2:\operatorname{Fin}(c_2)\to\iota}
--   G\bigl(w(J_1),w(J_2)\bigr).
--   $$
--
--   The formal functions `maskCount` and `selected` specify the two lists and their lengths. This is a combinatorial reindexing tool for cumulant-energy decompositions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L168-L234 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic`, declaration `FunctionalInequalities.KLS.BKL.sum_selected_eq`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section S4Section6Pointwise
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.BKL
variable {n : ℕ}
section Masks

theorem FunctionalInequalities.KLS.BKL.sum_selected_eq_408915f {E ι : Type*} [Fintype ι] (w : ι → E) :
    ∀ (k : ℕ) (q : Fin k → Bool) (G : List E → List E → ℝ) (c₁ c₂ : ℕ),
      maskCount q = c₁ → maskCount (fun i => !(q i)) = c₂ →
      ∑ J : Fin k → ι, G (selected (fun i => w (J i)) q)
          (selected (fun i => w (J i)) (fun i => !(q i))) =
        ∑ J₁ : Fin c₁ → ι, ∑ J₂ : Fin c₂ → ι,
          G (List.ofFn fun i => w (J₁ i)) (List.ofFn fun i => w (J₂ i)) := by sorry
