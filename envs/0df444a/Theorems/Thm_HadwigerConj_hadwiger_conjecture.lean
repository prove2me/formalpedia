-- Prove2me | Theorems.Thm_HadwigerConj_hadwiger_conjecture
-- name    : HadwigerConj.hadwiger_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T00:27:59.316777+00:00
-- url     : https://prove2.me/theorems/0b18177b-99d0-4532-b8a1-d52784d7d11c
-- title:
--   Hadwiger's conjecture
-- statement:
--   **Hadwiger's conjecture (1943).** For every integer $t\ge 0$, every finite graph $G$ with no $K_{t+1}$ minor is $t$-colourable:
--
--   $$\forall t\ge 0:\quad K_{t+1}\not\preceq G\ \Longrightarrow\ \chi(G)\le t.$$
--
--   Equivalently, every graph with chromatic number at least $t+1$ has $t+1$ pairwise disjoint connected vertex sets, every two joined by an edge. The conjecture is open for $t\ge 6$; it contains the four-colour theorem as the case $t=4$.
--
--   **Formalization Note** Stated as $\mathrm{HC}(t)$ for all natural numbers $t$, with $\mathrm{HC}$ from the definitions file; graphs are finite simple graphs.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), statement 1.1 (p. 2); Wikipedia, "Hadwiger conjecture (graph theory)", https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory), lead section

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem hadwiger_conjecture (t : ℕ) : HC t := by sorry
end HadwigerConj
