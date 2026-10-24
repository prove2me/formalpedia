-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_assemble_generator_408915f
-- name    : FunctionalInequalities.Analysis.assemble_generator_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:18:26.491989+00:00
-- url     : https://prove2.me/theorems/2d018f96-f04f-4628-a4c1-9262e6682449
-- title:
--   Assembly of the Weak Generator Identity
-- statement:
--   This is a private assembly lemma for a weak inverse-Hessian generator identity.
--
--   Let $u,V,a,f$ be functions on $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))$. Assume $u,V$ are $C^1$, $\nabla u$ is Lipschitz, the exponent $-u+V\circ\nabla u$ is Lipschitz, and almost everywhere
--   $$\det(\operatorname{hessianMatrix}(u,x))=e^{-u(x)+V(\nabla u(x))}.$$
--   Assume also that each weighted coordinate test has a Lipschitz compactly supported representative, that its coordinate derivative satisfies the specified a.e. formula, and that the associated `energyDensity u a f` is integrable.
--
--   Then
--   $$\int \operatorname{generatorDensity}(u,V,a,f)\,d\operatorname{vol}
--   =-\int \operatorname{energyDensity}(u,a,f)\,d\operatorname{vol}.$$
--
--   The statement is an internal analytic assembly interface: its hypotheses include the derivative and integrability inputs explicitly, and it does not itself assert the broader Monge–Ampère theorem.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L602-L742 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak.0.FunctionalInequalities.Analysis.assemble_generator`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
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
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
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
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
section GeneratorIdentities
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

lemma FunctionalInequalities.Analysis.assemble_generator_408915f {n : ℕ}
    {u V a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (ht : ∀ i, ∃ L : NNReal,
      LipschitzWith L (FunctionalInequalities.Analysis.weightedTest u a f i) ∧
        HasCompactSupport (FunctionalInequalities.Analysis.weightedTest u a f i))
    (hd : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j,
      FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.weightedTest u a f i) j x =
        Real.exp (-u x) *
          (FunctionalInequalities.Analysis.coord a j x * FunctionalInequalities.Analysis.coord f i x -
            a x * FunctionalInequalities.Analysis.coord u j x * FunctionalInequalities.Analysis.coord f i x +
            a x * hessianMatrix f x j i))
    (hE : Integrable (FunctionalInequalities.Analysis.energyDensity u a f)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∫ x, FunctionalInequalities.Analysis.generatorDensity u V a f x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -∫ x, FunctionalInequalities.Analysis.energyDensity u a f x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
