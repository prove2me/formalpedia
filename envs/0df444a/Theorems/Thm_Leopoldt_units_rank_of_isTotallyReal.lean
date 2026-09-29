-- Prove2me | Theorems.Thm_Leopoldt_units_rank_of_isTotallyReal
-- name    : Leopoldt.units_rank_of_isTotallyReal
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:41:36.6571+00:00
-- url     : https://prove2.me/theorems/3eb85439-60d5-4d3b-a9c3-a27055e26cc9
-- title:
--   Unit rank of a totally real field: $r = [K:\mathbb{Q}] - 1$
-- statement:
--   Let $K$ be a totally real number field. Then its unit group $\mathcal{O}_K^\times$ has $\mathbb{Z}$-rank
--   $$\operatorname{rk}_{\mathbb{Z}} \mathcal{O}_K^\times = [K:\mathbb{Q}] - 1.$$
--
--   This is Dirichlet's unit theorem $r = r_1 + r_2 - 1$ with $r_2 = 0$ and $r_1 = [K:\mathbb{Q}]$.
-- source:
--   Dirichlet's unit theorem, e.g. J. Neukirch, Algebraic Number Theory, Chapter I, Theorem 7.4, specialised to r_2 = 0; used in arXiv:1105.4544 Section 1.1

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem units_rank_of_isTotallyReal (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    Units.rank K = Module.finrank ℚ K - 1 := by sorry
end Leopoldt
