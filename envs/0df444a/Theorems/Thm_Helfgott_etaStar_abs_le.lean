-- Prove2me | Theorems.Thm_Helfgott_etaStar_abs_le
-- name    : Helfgott.etaStar_abs_le
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T21:26:28.832129+00:00
-- url     : https://prove2.me/theorems/a2949add-a122-42dc-a401-1a2b79278345
-- title:
--   Uniform bound for the coordinated Mellin smoothing
-- statement:
--   For η*(t)=(η₂ *_M φ)(49t), with φ(t)=t² exp(−t²/2), the absolute value is at most 1.414 for every real t. This uniform bound is used in the removal of proper prime-power and even-prime terms.
-- source:
--   Helfgott, arXiv:1312.7748v2, equations (4.7), (4.10), final section-7 smoothing definitions and equation (7.19). https://arxiv.org/html/1312.7748v2 . Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_PrimePowerRemoval
open scoped BigOperators

namespace Helfgott

theorem etaStar_abs_le (t : ℝ) : |etaStar t| ≤ (707 / 500 : ℝ) := by sorry

end Helfgott
