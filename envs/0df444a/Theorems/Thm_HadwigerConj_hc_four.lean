-- Prove2me | Theorems.Thm_HadwigerConj_hc_four
-- name    : HadwigerConj.hc_four
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T23:17:01.003008+00:00
-- url     : https://prove2.me/theorems/c01f0340-5cac-4cff-9e45-7e844b436e7c
-- title:
--   $\mathrm{HC}(4)$: graphs with no $K_5$ minor are $4$-colourable
-- statement:
--   Every finite graph with no $K_5$ minor is $4$-colourable:
--
--   $$K_5\not\preceq G\ \Longrightarrow\ \chi(G)\le 4.$$
--
--   Wagner (1937) showed that this statement is equivalent to the four-colour theorem; it became a theorem with the proof of the four-colour theorem by Appel and Haken (1976).
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Section 1 (p. 2) and Section 2, Theorem 2.2 and the paragraph after it (p. 3); Wikipedia, "Hadwiger conjecture (graph theory)", https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory), section “Special cases and partial results”

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem hc_four : HC 4 := by sorry
end HadwigerConj
