-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_weak_hessian_evolution_408915f
-- name    : FunctionalInequalities.Analysis.exists_regular_moment_weak_hessian_evolution_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:24:15.983359+00:00
-- url     : https://prove2.me/theorems/3daf1f09-ab05-4a6d-ab95-d574669f036c
-- title:
--   Regular Moment Witness with Weak Hessian Evolution
-- statement:
--   This formalizes part of Lemma 2.4 of Letwin (arXiv:2607.24164v1), locator Lemma 2.4, by extending the regular moment witness with weak Hessian evolution data.
--
--   Assume $n>0$, $\kappa>0$, $K$ is compact, convex, and has nonempty interior, $W$ is smooth, and $W(y)-\frac\kappa2\|y\|^2$ is convex on all of $\mathbb R^n$. Let $\mu$ be a probability measure whose density is $e^{-W}$ on $K$ and zero outside $K$, and assume that $\mu$ is isotropic.
--
--   Then there exist $u:\mathbb R^n\to\mathbb R$, $L,LF\in[0,\infty)$, and a tensor $T_{kij}$ such that the previously established regular moment properties hold: $u$ is convex and Lipschitz, $\int e^{-u}=1$, the tilted measure $e^{-u}dx$ pushed forward by $\nabla u$ equals $\mu$, $u$ is $C^1$, $\nabla u$ is Lipschitz with constant $\operatorname{toNNReal}(16/\kappa)$, and $-u+W\circ\nabla u$ is Lipschitz. Moreover,
--
--   $$
--   u:=e^{-u}dx
--   $$
--   is the normalized tilted measure, and
--
--   $$
--    u(x+h)+u(x-h)-2u(x)\le \frac4\kappa\|h\|^2.
--   $$
--
--   Almost everywhere, $\nabla^2u$ is positive definite,
--   $$
--   \log\det\nabla^2u=-u+W(\nabla u),
--   \qquad
--   \frac{16}{\kappa}I-\nabla^2u\succeq0.
--   $$
--
--   The tensor $T$ is a compact-local $L^2$ weak derivative of the Hessian. The declaration also supplies a Lipschitz representative for $e^{-u+W(\nabla u)}$, weak derivatives and compact-local bounds for the determinant and log determinant, the inverse-Hessian weak derivative formula with local $L^2$ and `ENNReal` local $L^\infty$ bounds, integrability and mean identity
--   $$
--   \int (\nabla^2u)_{ij}\,d\nu=\delta_{ij},
--   $$
--   the weak derivative of the first Monge–Ampère trace, the unweighted flux identity, and the weighted curvature–Gram identity stated above.
--
--   This existential declaration packages the complete regular witness needed by later weak evolution and testing results. It asserts existence of these data, not a universal estimate.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakHessian.lean#L338-L502 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian`, declaration `FunctionalInequalities.Analysis.exists_regular_moment_weak_hessian_evolution`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Stein_Kernel
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
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Bases
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

section RegularSource
open MeasureTheory Set
open scoped ContDiff
variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein
section RegularMomentWeakHessianEvolution
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
include hn hκ hK hKc hKint hW hstrong hμ hiso

theorem FunctionalInequalities.Analysis.exists_regular_moment_weak_hessian_evolution_408915f :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      (∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))) ∧
      (∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
    (let Q := fun x i j => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
  (    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by sorry
