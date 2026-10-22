-- Prove2me | Theorems.Thm_Milne_zeta_point
-- name    : Milne.zeta_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-20T03:12:39.213986+00:00
-- url     : https://prove2.me/theorems/0dfc0963-0a3e-41a6-8f65-bb8eb432547b
-- title:
--   The zeta function of a point is the geometric series
-- statement:
--   A variety with exactly one point over every extension field has zeta function Z(X, t) = 1/(1 − t): every Taylor coefficient of the zeta function attached to the constant point-count sequence is 1 (Section 7 of the source: Z(P⁰, t) = 1/(1 − t)).
-- source:
--   J. S. Milne, Motives — Grothendieck's Dream, v2.04, April 2012, Section 7 (p. 10): Z(P⁰, t) = 1/(1 − t).

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta

namespace Milne

/-- The zeta function of a point (section 7 of the paper): a variety with
exactly one point over every extension field has zeta function
Z(X, t) = 1/(1 − t); every Taylor coefficient of the zeta function
attached to the constant count sequence is 1. -/
theorem zeta_point (n : ℕ) :
    zetaCoeff (fun _ => (1 : ℚ)) n = 1 := by
  sorry

end Milne
