-- Prove2me | Theorems.Thm_Leopoldt_units_rank_of_isTotallyComplex
-- name    : Leopoldt.units_rank_of_isTotallyComplex
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:41:19.626215+00:00
-- url     : https://prove2.me/theorems/fac2ede9-9178-4871-864b-4fcd1254e5b1
-- title:
--   Unit rank of a totally complex field: $r = [K:\mathbb{Q}]/2 - 1$
-- statement:
--   Let $K$ be a totally complex number field (for example a CM field). Then its unit group has $\mathbb{Z}$-rank
--   $$\operatorname{rk}_{\mathbb{Z}} \mathcal{O}_K^\times = \frac{[K:\mathbb{Q}]}{2} - 1.$$
--
--   This is Dirichlet's unit theorem $r = r_1 + r_2 - 1$ with $r_1 = 0$ and $2 r_2 = [K:\mathbb{Q}]$.
-- source:
--   Dirichlet's unit theorem, e.g. J. Neukirch, Algebraic Number Theory, Chapter I, Theorem 7.4, specialised to r_1 = 0; used in arXiv:1105.4544 Section 1.1 for CM fields

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem units_rank_of_isTotallyComplex (K : Type*) [Field K] [NumberField K]
    [IsTotallyComplex K] :
    Units.rank K = Module.finrank ℚ K / 2 - 1 := by sorry
end Leopoldt
