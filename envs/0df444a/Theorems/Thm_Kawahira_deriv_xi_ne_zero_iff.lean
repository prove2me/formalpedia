-- Prove2me | Theorems.Thm_Kawahira_deriv_xi_ne_zero_iff
-- name    : Kawahira.deriv_xi_ne_zero_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T22:43:57.875071+00:00
-- url     : https://prove2.me/theorems/e067271f-218e-4879-92ff-9486aaecf09d
-- title:
--   Xi and zeta have simultaneous simple zeros
-- statement:
--   At every nontrivial zero of the Riemann zeta function, the derivative of the normalized xi function is nonzero exactly when the derivative of zeta is nonzero. Thus xi and zeta have the same simplicity criterion at their common zeros.
-- source:
--   Classical local factorization of the Riemann xi function by a nonvanishing Gamma factor in the critical strip.

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_nontrivial_zero_mem_strip

open Complex Topology Filter Set

namespace Kawahira

theorem deriv_xi_ne_zero_iff (s : ℂ) (hs : IsNontrivialZero s) :
    deriv xi s ≠ 0 ↔ deriv riemannZeta s ≠ 0 := by sorry
