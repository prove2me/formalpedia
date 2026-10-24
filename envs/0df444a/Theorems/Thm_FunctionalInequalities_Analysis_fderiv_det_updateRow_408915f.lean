-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_fderiv_det_updateRow_408915f
-- name    : FunctionalInequalities.Analysis.fderiv_det_updateRow_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:12:08.822587+00:00
-- url     : https://prove2.me/theorems/9879eb2f-defc-4d61-9364-122e19ab5980
-- title:
--   Derivative of a Determinant with One Updated Row
-- statement:
--   This private lemma is a technical determinant differentiation formula.
--
--   Let $E$ be a real normed vector space, let $A:E\to\operatorname{Fin}(n)\to\operatorname{Fin}(n)\to\mathbb R$, and suppose every scalar entry $y\mapsto A(y)_{kl}$ is differentiable at $x\in E$. Fix a row $j$, a replacement row $c:\operatorname{Fin}(n)\to\mathbb R$, and a direction $v\in E$. Then
--
--   $$D\left[y\mapsto\det(\operatorname{updateRow}(A(y),j,c))\right]_x(v)
--   =\sum_k \begin{cases}0,&k=j,\\
--   \det\bigl(\operatorname{updateRow}(\operatorname{updateRow}(A(x),j,c),k,D(A_{k\bullet})_x(v))\bigr),&k\ne j.
--   \end{cases}$$
--
--   The declaration `fderiv_det_updateRow` is used as a local algebraic rule and makes no symmetry, positivity, or invertibility assumption on the matrices.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L57-L129 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Piola`, declaration `_private.FunctionalInequalities.Analysis.Matrix.Piola.0.FunctionalInequalities.Analysis.fderiv_det_updateRow`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open Matrix
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

lemma FunctionalInequalities.Analysis.fderiv_det_updateRow_408915f
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Fin n → Fin n → ℝ) (x : E)
    (hA : ∀ k l, DifferentiableAt ℝ (fun y => A y k l) x)
    (j : Fin n) (c : Fin n → ℝ) (v : E) :
    fderiv ℝ (fun y => (Matrix.updateRow (A y) j c).det) x v =
      ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv ℝ (fun y => A y k l) x v)).det := by sorry
