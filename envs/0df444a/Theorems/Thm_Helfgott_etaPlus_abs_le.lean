-- Prove2me | Theorems.Thm_Helfgott_etaPlus_abs_le
-- name    : Helfgott.etaPlus_abs_le
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T21:26:20.113579+00:00
-- url     : https://prove2.me/theorems/2c1a2193-c590-4f70-8e9e-7545bef7a3d4
-- title:
--   Uniform bound for the final major-arc smoothing
-- statement:
--   The absolute value of Helfgott’s final smoothing η+(t)=h_200(t)t exp(−t²/2) is at most 1.079955 for all real t. The use of an absolute value allows the Mellin-band-limited approximation to change sign. This is the uniform estimate used in the prime-power removal step.
-- source:
--   Helfgott, arXiv:1312.7748v2, final smoothing definitions at the start of section 7 and equation (7.3), using the estimates of Major arcs for Goldbach’s problem, arXiv:1305.2897, Appendix B.5. https://arxiv.org/html/1312.7748v2 . Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_PrimePowerRemoval
open scoped BigOperators

namespace Helfgott

theorem etaPlus_abs_le (t : ℝ) : |etaPlus t| ≤ (1079955 / 1000000 : ℝ) := by sorry

end Helfgott
