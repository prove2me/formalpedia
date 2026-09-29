-- Prove2me | Theorems.Thm_Leopoldt_zpRankBelow_unitClosure_eq_of_units_rank_le
-- name    : Leopoldt.zpRankBelow_unitClosure_eq_of_units_rank_le
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:41:15.104025+00:00
-- url     : https://prove2.me/theorems/8ee5d2de-d45d-4ddd-9e6e-18dea7f62c74
-- title:
--   The $\mathbb{Z}_p$-rank of $\bar E$ does not depend on the bound once it exceeds the unit rank
-- statement:
--   Let $K$ be a number field, $p$ a prime, $U = \prod_{\wp \mid p} \mathcal{O}_\wp^\times$ the semilocal units and $\bar E \subseteq U$ the $p$-adic closure of the global units. For a bound $b$, let $\operatorname{rk}_b(\bar E)$ be the largest $n \le b$ such that $\mathbb{Z}_p^{\,n}$ embeds continuously and injectively into $U$ with image in $\bar E$ (`zpRankBelow p b (unitClosure p K)`).
--
--   If $b \ge r = \operatorname{rk}_{\mathbb{Z}} \mathcal{O}_K^\times$ (Dirichlet's unit rank $r_1 + r_2 - 1$), then
--   $$\operatorname{rk}_b(\bar E) = \operatorname{rk}_{[K:\mathbb{Q}]}(\bar E).$$
--
--   So the bound $[K:\mathbb{Q}]$ used in the definition of the Leopoldt defect can be replaced by any bound at least the unit rank, and the $\mathbb{Z}_p$-rank of $\bar E$ is intrinsic.
-- source:
--   Mission definition file Def_LeopoldtDefect (definition of zpRankBelow), after P. Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, Section 1.1 (Notations and fundamental facts); Dirichlet's unit theorem; uses Leopoldt.zpRankBelow_unitClosure_le_units_rank and Leopoldt.le_finrank_of_continuous_injective_semilocalUnits

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem zpRankBelow_unitClosure_eq_of_units_rank_le (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] {b : ℕ} (hb : Units.rank K ≤ b) :
    zpRankBelow p b (unitClosure p K) =
      zpRankBelow p (Module.finrank ℚ K) (unitClosure p K) := by sorry
end Leopoldt
