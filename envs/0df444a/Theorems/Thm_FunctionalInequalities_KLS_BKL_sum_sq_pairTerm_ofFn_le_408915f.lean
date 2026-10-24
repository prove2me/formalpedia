-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_sum_sq_pairTerm_ofFn_le_408915f
-- name    : FunctionalInequalities.KLS.BKL.sum_sq_pairTerm_ofFn_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:16:49.038944+00:00
-- url     : https://prove2.me/theorems/5f1a8aa4-ddb7-4313-b5fb-eed6cf563ccd
-- title:
--   Row Contraction Bound for Pair Terms
-- statement:
--   This formalizes the row-contraction estimate corresponding to BKL (101)–(102).
--
--   Let $\nu$ be a compactly supported probability measure on $\mathbb{R}^n$ whose covariance operator $A$ is invertible and strictly positive in every nonzero direction. Let $c,c_2\in\mathbb{N}$, let $\beta\in\mathbb{R}$, and assume that for every $v\in\mathbb{R}^n$,
--
--   $$
--   E_{c_2}(v)\le \beta\langle Av,v\rangle,
--   $$
--
--   where $E_j$ is the formalized `cumulantEnergy`. Then, for every $u\in\mathbb{R}^n$,
--
--   $$
--   \sum_{J_1:\operatorname{Fin}(c)\to\operatorname{Fin}(n)}
--   \sum_{J_2:\operatorname{Fin}(c_2)\to\operatorname{Fin}(n)}
--   \operatorname{pairTerm}(\nu,u;J_1,J_2)
--   \le \beta E_{c+1}(u).
--   $$
--
--   The lists in the pair term use the covariance-normalized basis `sigmaBasis`. This is the one-mask contraction estimate used in the lower-drift bound.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L382-L430 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic`, declaration `FunctionalInequalities.KLS.BKL.sum_sq_pairTerm_ofFn_le`; the repository is private at upload time).

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

theorem FunctionalInequalities.KLS.BKL.sum_sq_pairTerm_ofFn_le_408915f (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hA : IsUnit (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    {c c₂ : ℕ} (β : ℝ)
    (h100 : ∀ v : EuclideanSpace ℝ (Fin n),
      cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) c₂ v ≤
        β * ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (u : EuclideanSpace ℝ (Fin n)) :
    ∑ J₁ : Fin c → Fin n, ∑ J₂ : Fin c₂ → Fin n,
      pairTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) u
        (List.ofFn fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₁ i))
        (List.ofFn fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₂ i)) ≤
      β * cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (c + 1) u := by sorry
