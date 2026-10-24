-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_trace_mul_of_mean_one_408915f
-- name    : FunctionalInequalities.Analysis.integral_trace_mul_of_mean_one_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:08.940611+00:00
-- url     : https://prove2.me/theorems/80bf8794-5305-439a-a711-eab979d06c10
-- title:
--   Integral Of A Trace Against A Mean Identity Matrix
-- statement:
--   This statement describes integration of a matrix trace against a matrix field whose entrywise mean is the identity.
--
--   Let Ω be a measurable space, ρ a measure on Ω, and ι a finite index type with decidable equality. Let H:Ω→Matrix(ι,ι,ℝ). Assume every entry $H_{ij}$ is integrable and has mean
--
--   $$\int H(y)_{ij}\,d\rho=(I)_{ij}.$$
--
--   Then for every real matrix B, the function $y\mapsto\operatorname{tr}(BH(y))$ is integrable and
--
--   $$\int\operatorname{tr}(BH(y))\,d\rho=\operatorname{tr}(B).$$
--
--   This is a finite-coordinate linearity lemma for matrix-valued integration.
--
--   **Formalization Note** The hypothesis is entrywise and does not require H or B to be symmetric, positive, or measurable as a bundled matrix-valued function.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Integral.lean#L188-L219 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Integral`, declaration `FunctionalInequalities.Analysis.integral_trace_mul_of_mean_one`; the repository is private at upload time).

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section
open Matrix MeasureTheory
noncomputable section
open MeasureTheory Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 400000

theorem FunctionalInequalities.Analysis.integral_trace_mul_of_mean_one_408915f {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (ρ : Measure Ω) (H : Ω → Matrix ι ι ℝ)
    (hInt : ∀ i j, Integrable (fun y => H y i j) ρ)
    (hmean : ∀ i j, (∫ y, H y i j ∂ρ) = (1 : Matrix ι ι ℝ) i j)
    (B : Matrix ι ι ℝ) :
    Integrable (fun y => Matrix.trace (B * H y)) ρ ∧
      (∫ y, Matrix.trace (B * H y) ∂ρ) = Matrix.trace B := by sorry
