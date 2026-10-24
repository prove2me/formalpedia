-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_compact_ordinary_diffusion_coercivity_of_lipschitz_gradient_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.compact_ordinary_diffusion_coercivity_of_lipschitz_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:53.929961+00:00
-- url     : https://prove2.me/theorems/c9b8a48b-ea78-486a-9adf-9e1b857a7b94
-- title:
--   Ordinary Diffusion Coercivity with Lipschitz Gradient
-- statement:
--   This is the coercivity consequence of the integrated Bochner identity at Lipschitz regularity; it is related to Lemma A.6 of Letwin (2026).
--
--   Let $E$ be a complete finite-dimensional real inner-product space with its Borel structure. Let $U:E\to\mathbb R$ be $C^1$, with $\nabla U$ Lipschitz with constant $G\in[0,\infty)$ and $U$ Lipschitz with constant $L\in[0,\infty)$. Assume $e^{-U}$ is integrable with respect to volume measure. Let $f:E\to\mathbb R$ be smooth and compactly supported, and set $\nu=\operatorname{volume}.\operatorname{tilted}(-U)$. Then:
--
--   1. The function $x\mapsto\langle D(\nabla U)(x)\nabla f(x),\nabla f(x)\rangle$ is $\nu$-integrable.
--   2. The function $x\mapsto(\mathcal L_Uf(x))^2$ is $\nu$-integrable.
--   3. The Hessian pairing is bounded above by the squared weighted Laplacian:
--
--   $$
--   \int\left\langle D(\nabla U)\nabla f,\nabla f\right\rangle d\nu
--   \leq
--   \int(\mathcal L_Uf)^2d\nu.
--   $$
--
--   This supplies an ordinary diffusion coercivity estimate without a pointwise Hessian lower bound.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.6. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Lipschitz.lean#L285-L343 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Lipschitz`, declaration `FunctionalInequalities.Analysis.BakryEmery.compact_ordinary_diffusion_coercivity_of_lipschitz_gradient`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace
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
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 2000000

theorem FunctionalInequalities.Analysis.BakryEmery.compact_ordinary_diffusion_coercivity_of_lipschitz_gradient_408915f
    {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal}
    (hG : LipschitzWith G (gradient U)) {L : NNReal} (hL : LipschitzWith L U)
    (hexp : Integrable (fun x => Real.exp (-U x)) (volume : Measure E))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Integrable (fun x => ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫)
      ((volume : Measure E).tilted (-U)) ∧
    Integrable (fun x => weightedLaplacian U f x ^ 2)
      ((volume : Measure E).tilted (-U)) ∧
    (∫ x, ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫
        ∂((volume : Measure E).tilted (-U))) ≤
      ∫ x, weightedLaplacian U f x ^ 2 ∂((volume : Measure E).tilted (-U)) := by sorry
