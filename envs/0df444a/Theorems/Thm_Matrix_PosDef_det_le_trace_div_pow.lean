-- Prove2me | Theorems.Thm_Matrix_PosDef_det_le_trace_div_pow
-- name    : Matrix.PosDef.det_le_trace_div_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:37.36595+00:00
-- url     : https://prove2.me/theorems/29fb45b4-5abe-48e5-83a2-19dd2933d7c2
-- title:
--   `det V ≤ (trace V / d) ^ d` for a positive definite matrix
-- statement:
--   Let $V$ be a positive definite real $d \times d$ matrix, $d \ge 1$. Then
--
--   $$
--   \det V \;\le\; \Bigl(\frac{\operatorname{tr} V}{d}\Bigr)^{d}.
--   $$
--
--   This is the matrix form of the arithmetic–geometric mean inequality: the determinant is the
--   product and the normalized trace the arithmetic mean of the eigenvalues, all of which are
--   positive. Equality holds exactly when $V$ is a multiple of the identity.
--
--   The inequality is the standard way to convert a bound on a trace — which is additive and
--   therefore easy to accumulate over the steps of an algorithm — into a bound on a
--   determinant, which is what appears in the elliptical potential and self-normalized
--   concentration arguments used for linear bandit and least-squares regret analyses.
-- source:
--   R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., CUP 2013, §7.8 (determinant–trace inequality); carved from the accepted proof of ImprovedLinBandits.OFUL.oful_regret_bound, https://prove2.me/submissions/028e111f-382d-40d0-8008-127228d5e6cf

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Matrix NNReal

theorem Matrix.PosDef.det_le_trace_div_pow {d : ℕ} (hd : 0 < d) {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) :
    V.det ≤ (V.trace / d) ^ d := by sorry
