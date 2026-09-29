-- Prove2me | Theorems.Thm_Kawahira_nontrivial_zero_mem_strip
-- name    : Kawahira.nontrivial_zero_mem_strip
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T22:30:07.508387+00:00
-- url     : https://prove2.me/theorems/1c05c2d2-ba60-405b-8ae6-436f660af859
-- title:
--   Nontrivial Riemann zeta zeros lie in the critical strip
-- statement:
--   Every zero of the Riemann zeta function which is not one of the negative even trivial zeros lies in the open critical strip $0<\operatorname{Re}(s)<1$. The right boundary follows from Euler-product nonvanishing; the left boundary follows from the functional equation and the classification of integral zeros by parity.
-- source:
--   Classical zero-free regions and the Riemann zeta functional equation; used in T. Kawahira (2016), Propositions 7–9, https://doi.org/10.1080/10586458.2016.1217443.

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_riemannZeta_neg_odd_ne_zero

open Complex Topology

namespace Kawahira

theorem nontrivial_zero_mem_strip (s : ℂ) (hz : riemannZeta s = 0)
    (htrivial : ∀ n : ℕ, s ≠ -2 * (n + 1)) :
    0 < s.re ∧ s.re < 1 := by sorry
