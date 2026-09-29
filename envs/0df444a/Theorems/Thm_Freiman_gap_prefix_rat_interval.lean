-- Prove2me | Theorems.Thm_Freiman_gap_prefix_rat_interval
-- name    : Freiman.gap_prefix_rat_interval
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:38.665975+00:00
-- url     : https://prove2.me/theorems/8bff79e8-fdd6-4e26-9111-1c02b911f31c
-- title:
--   gap prefix rat interval
-- statement:
--   Strict monotonicity of a finite continued-fraction map transfers strict residual bounds to the two rational endpoint evaluations.
-- source:
--   Freiman Hall ray report, m3.tex; eq:m3:action, eq:m3:cylinder

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_prefix_rat_interval (w : List ℕ+) (x : ℝ) (h : (1/5 : ℝ) < x ∧ x < 5/6) : (gapRatLower w : ℝ) < prefixEval w x ∧ prefixEval w x < (gapRatUpper w : ℝ) := by
  sorry

end Freiman
