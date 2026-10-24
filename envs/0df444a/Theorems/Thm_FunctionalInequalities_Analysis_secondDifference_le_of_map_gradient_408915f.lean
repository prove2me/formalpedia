-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_secondDifference_le_of_map_gradient_408915f
-- name    : FunctionalInequalities.Analysis.secondDifference_le_of_map_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:50.995211+00:00
-- url     : https://prove2.me/theorems/ae472d0a-75d6-42bc-a53a-5cf0b0d3efa8
-- title:
--   Centered Difference Bound for Moment-Map Potentials
-- statement:
--   This formalizes the centered-difference estimate associated with regularity of the moment map, cited in Lemma 2.2 of Letwin2026 (Klartag [41]).
--
--   Let $u,V:\mathbb R^n\to\mathbb R$, let $L\in[0,\infty)$, and assume:
--
--   1. $u$ is $L$-Lipschitz and convex;
--   2. $\int e^{-u(x)}\,dx=1$;
--   3. $K\subset\mathbb R^n$ is compact and convex;
--   4. $V$ is $C^1$ and $V(y)-\frac\kappa2\|y\|^2$ is convex for some $\kappa>0$;
--   5. the pushforward of the tilted volume measure with density $e^{-u}$ under $\nabla u$ equals the measure with density $e^{-V}$ on $K$;
--   6. $u$ is $C^1$.
--
--   Then, for every $x,h\in\mathbb R^n$,
--
--   $$
--   u_h^2u(x):=u(x+h)+u(x-h)-2u(x)
--   \leq \frac{4}{\kappa}\|h\|^2.
--   $$
--
--   This exports the exact coefficient used in the subsequent Lipschitz-gradient regularity argument.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.2 (Klartag [41]). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/GradientLipschitz.lean#L88-L174 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.GradientLipschitz`, declaration `FunctionalInequalities.Analysis.secondDifference_le_of_map_gradient`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
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
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.EReal.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.secondDifference_le_of_map_gradient_408915f {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hV : ContDiff ℝ 1 V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hC1 : ContDiff ℝ 1 u) :
    ∀ x h : EuclideanSpace ℝ (Fin n),
      u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2 := by sorry
