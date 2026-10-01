-- Prove2me | Theorems.Thm_HadwigerConj_hc_of_le_three
-- name    : HadwigerConj.hc_of_le_three
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T23:12:08.760995+00:00
-- url     : https://prove2.me/theorems/8589461b-5d7b-4a94-8a89-2e797ca6cc38
-- title:
--   $\mathrm{HC}(t)$ for $t\le 3$ (Hadwiger 1943)
-- statement:
--   For $0\le t\le 3$, every finite graph with no $K_{t+1}$ minor is $t$-colourable:
--
--   $$t\le 3\ \Longrightarrow\ \mathrm{HC}(t).$$
--
--   The cases $t\le 1$ are trivial, $t=2$ is the statement that forests are $2$-colourable, and $t=3$ (graphs with no $K_4$ minor are $3$-colourable) was proved by Hadwiger when he posed the conjecture.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Section 1 (p. 2, “Hadwiger proved HC(t) for t ≤ 3 in 1943”) and Section 2 (p. 2); Wikipedia, "Hadwiger conjecture (graph theory)", https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory), section “Special cases and partial results”

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem hc_of_le_three (t : ℕ) (ht : t ≤ 3) : HC t := by sorry
end HadwigerConj
