-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_trace_mul_of_mean_one_readable
-- name    : FunctionalInequalities.Analysis.integral_trace_mul_of_mean_one_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:50.614531+00:00
-- url     : https://prove2.me/theorems/0fa1db57-6ad5-4665-9a1e-3a5d91a7bc2b
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 400000 in
--   theorem integral_trace_mul_of_mean_one {Ω ι : Type*} [MeasurableSpace Ω]
--       [Fintype ι] [DecidableEq ι] (ρ : Measure Ω) (H : Ω → Matrix ι ι ℝ)
--       (hInt : ∀ i j, Integrable (fun y => H y i j) ρ)
--       (hmean : ∀ i j, (∫ y, H y i j ∂ρ) = (1 : Matrix ι ι ℝ) i j)
--       (B : Matrix ι ι ℝ) :
--       Integrable (fun y => Matrix.trace (B * H y)) ρ ∧
--         (∫ y, Matrix.trace (B * H y) ∂ρ) = Matrix.trace B
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Integral`](https://prove2.me/theorems/09aa8c12-3230-447e-89a1-dc642659f2aa).
--
--   Previous: [`symmetric_trace_integral_extension_mul_of_ae_posSemidef`](https://prove2.me/theorems/bb367c0f-60b7-46e5-bbe8-0f5d9f6169fc).
--
--   [Source excerpt, lines 188–195](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Integral.lean#L188-L195) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Integral.lean#L188-L219 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Integral`, declaration `FunctionalInequalities.Analysis.integral_trace_mul_of_mean_one`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Integral

open MeasureTheory Matrix
set_option maxHeartbeats 400000

theorem FunctionalInequalities.Analysis.integral_trace_mul_of_mean_one_readable {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (ρ : Measure Ω) (H : Ω → Matrix ι ι ℝ)
    (hInt : ∀ i j, Integrable (fun y => H y i j) ρ)
    (hmean : ∀ i j, (∫ y, H y i j ∂ρ) = (1 : Matrix ι ι ℝ) i j)
    (B : Matrix ι ι ℝ) :
    Integrable (fun y => Matrix.trace (B * H y)) ρ ∧
      (∫ y, Matrix.trace (B * H y) ∂ρ) = Matrix.trace B := by sorry
