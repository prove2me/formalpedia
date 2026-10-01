-- Prove2me | Theorems.Thm_HadwigerConj_hc_five
-- name    : HadwigerConj.hc_five
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T23:24:37.964795+00:00
-- url     : https://prove2.me/theorems/8c6943ca-598b-47b0-8962-0c7d8d6a0e60
-- title:
--   $\mathrm{HC}(5)$: graphs with no $K_6$ minor are $5$-colourable
-- statement:
--   Every finite graph with no $K_6$ minor is $5$-colourable:
--
--   $$K_6\not\preceq G\ \Longrightarrow\ \chi(G)\le 5.$$
--
--   Proved by Robertson, Seymour and Thomas (1993), assuming the four-colour theorem. It is the largest case of Hadwiger's conjecture currently known.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Section 1 (p. 2) and Section 2 (pp. 3–4); Wikipedia, "Hadwiger conjecture (graph theory)", https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory), section “Special cases and partial results”

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem hc_five : HC 5 := by sorry
end HadwigerConj
