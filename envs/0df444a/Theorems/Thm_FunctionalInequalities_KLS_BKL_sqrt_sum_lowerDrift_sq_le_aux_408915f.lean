-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_sqrt_sum_lowerDrift_sq_le_aux_408915f
-- name    : FunctionalInequalities.KLS.BKL.sqrt_sum_lowerDrift_sq_le_aux_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:16:38.673845+00:00
-- url     : https://prove2.me/theorems/99808200-e49f-454f-abd5-673f80a46679
-- title:
--   Pointwise Lower-Drift Square-Sum Bound
-- statement:
--   This is the Section 6 pointwise estimate with order parameter $m=k+1$.
--
--   Let $\nu$ be a compactly supported probability measure on $\mathbb{R}^n$ with invertible covariance operator that is strictly positive on nonzero vectors. Let $k\in\mathbb{N}$, let $b:\mathbb{N}\to\mathbb{R}$, and assume that for every $r$ with $2\le r<k+1$ and every $v$,
--
--   $$
--   E_{r-1}(v)\le b(r)\langle Av,v\rangle.
--   $$
--
--   Then for every $u\in\mathbb{R}^n$,
--
--   $$
--   \sqrt{\sum_{J:\operatorname{Fin}(k)\to\operatorname{Fin}(n)}
--   L(\nu)(u,\sigma e_{J_1},\ldots,\sigma e_{J_k})^2}
--   \le
--   \sum_{a\in[2,k-1]}
--   \binom{k}{a-1}
--   \sqrt{b(k+2-a)E_a(u)}.
--   $$
--
--   Here `lowerDrift`, `sigmaBasis`, and `cumulantEnergy` are the formalized quantities. The result supplies the pointwise middle-term estimate used in the cumulant-energy induction.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L432-L527 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic`, declaration `FunctionalInequalities.KLS.BKL.sqrt_sum_lowerDrift_sq_le_aux`; the repository is private at upload time).

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
section Algebra

theorem FunctionalInequalities.KLS.BKL.sqrt_sum_lowerDrift_sq_le_aux_408915f (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hA : IsUnit (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (k : ℕ) (b : ℕ → ℝ)
    (h100 : ∀ r, 2 ≤ r → r < k + 1 → ∀ v : EuclideanSpace ℝ (Fin n),
      cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (r - 1) v ≤
        b r * ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (u : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt (∑ J : Fin k → Fin n,
        lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n)))
          (Fin.cons u fun i => inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
            (EuclideanSpace.basisFun (Fin n) ℝ (J i)) : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) 0 ^ 2) ≤
      ∑ a ∈ Finset.Icc 2 (k - 1), (k.choose (a - 1) : ℝ) *
        Real.sqrt (b (k + 2 - a) * cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) a u) := by sorry
