-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_sum_integral_spectral_noise_energy_le_408915f
-- name    : FunctionalInequalities.KLS.LogConcave.sum_integral_spectral_noise_energy_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:26:24.734617+00:00
-- url     : https://prove2.me/theorems/2b24f7bf-21ce-4668-b910-09fc85c91c3b
-- title:
--   Spectral Noise Energy Bound
-- statement:
--   This is a finite-dimensional matrix-energy estimate with the trace bound supplied as a hypothesis.
--
--   Let $\rho$ and $\gamma$ be probability measures on measurable spaces $\Omega$ and $\Delta$. Let $H:\Omega\to\mathbb R^{n\times n}$ have measurable entries, be symmetric almost everywhere, have integrable entries, and have mean $I$. Assume that for every symmetric matrix $B$, $\operatorname{tr}(BH B H)$ is integrable and
--   $$\int\operatorname{tr}(BH(y)BH(y))\,d\rho(y)\le 2\operatorname{tr}(B^2).$$
--   Let $M$ be symmetric and invertible, and let $t\in\mathbb R$. Define $B=\sqrt{M^2}$, $S=\sqrt B$, and $Q=\operatorname{sign}(M)$. Then each coordinate energy is integrable and
--
--   $$\sum_i\int_{\Omega\times\Delta}\left\|(SH(y)S+tI)Qe_i\right\|^2\,d(\rho\otimes\gamma)
--   \le 2\operatorname{tr}(M^2)+2t\operatorname{tr}(B)+nt^2.$$
--
--   No log-concavity or Stein-kernel conclusion is part of the statement; the trace estimate is an input.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Stein/QuadraticAction.lean#L66-L145 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Stein.QuadraticAction`, declaration `FunctionalInequalities.KLS.LogConcave.sum_integral_spectral_noise_energy_le`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Stein_Kernel
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace MatrixOrder
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.KLS.LogConcave.sum_integral_spectral_noise_energy_le_408915f {n : ℕ} {Ω Δ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Δ] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (γ : Measure Δ) [IsProbabilityMeasure γ]
    (H : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hHmeas : ∀ i j, Measurable (fun y => H y i j))
    (hHsym : ∀ᵐ y ∂ρ, (H y).IsSymm)
    (hHint : ∀ i j, Integrable (fun y => H y i j) ρ)
    (hmean : ∀ i j, (∫ y, H y i j ∂ρ) = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hT25 : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
      Integrable (fun y => Matrix.trace (B*H y*B*H y)) ρ ∧
        (∫ y, Matrix.trace (B*H y*B*H y) ∂ρ) ≤ 2*Matrix.trace (B*B))
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hunit : IsUnit M) (t : ℝ) :
    let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M*M)
    let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
    let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    (∀ i : Fin n, Integrable (fun y => ‖action (S*H y*S + t • 1)
      (action Q (EuclideanSpace.single i 1))‖^2) ρ) ∧
    (∑ i : Fin n, ∫ p : Ω × Δ, ‖action (S*H p.1*S + t • 1)
      (action Q (EuclideanSpace.single i 1))‖^2 ∂ρ.prod γ) ≤
      2*Matrix.trace (M*M) + 2*t*Matrix.trace B + (n : ℝ)*t^2 := by sorry
