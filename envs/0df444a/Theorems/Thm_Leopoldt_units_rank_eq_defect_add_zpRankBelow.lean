-- Prove2me | Theorems.Thm_Leopoldt_units_rank_eq_defect_add_zpRankBelow
-- name    : Leopoldt.units_rank_eq_defect_add_zpRankBelow
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:20:33.137405+00:00
-- url     : https://prove2.me/theorems/e23b1366-ec20-4807-b18d-cdf0d00c1f35
-- title:
--   $\mathbb{Z}\text{-rk}(E) = \mathcal{D}_L(K) + \mathbb{Z}_p\text{-rk}(\overline{E})$
-- statement:
--   Let $p$ be a prime and $K$ a number field, with $E = \mathcal{O}_K^\times$ and $\overline{E}$ the $p$-adic closure of $\iota(E)$ in the semilocal units $U = \prod_{\wp\mid p}\mathcal{O}_{K_\wp}^\times$. Then Dirichlet's unit rank splits as the Leopoldt defect plus the $\mathbb{Z}_p$-rank of the closure:
--   $$\mathbb{Z}\text{-rk}(E) \;=\; \mathcal{D}_L(K) + \mathbb{Z}_p\text{-rk}(\overline{E}).$$
--
--   This is the defining relation $\mathcal{D}_L(K) = \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\overline{E})$ read as an identity of natural numbers; it holds exactly because $\mathbb{Z}_p\text{-rk}(\overline{E}) \le \mathbb{Z}\text{-rk}(E)$, so that the truncated subtraction used in the Lean definition of `defect` coincides with the true difference. It lets one move freely between statements about the defect and statements about the rank of $\overline{E}$.
--
--   **Formalization Note** `defect p K` is `Units.rank K - zpRankBelow p (finrank ℚ K) (unitClosure p K)` with truncated natural-number subtraction (`Definitions.Def_LeopoldtDefect`).
-- source:
--   P. Mihăilescu, On CM $\mathbb{Z}_p$-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 (Notations and fundamental facts): definition of the Leopoldt defect $\mathcal{D}_L(K) = \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\overline{E})$ as a non-negative integer (Leopoldt's conjecture: $\mathcal{D}_L(K)=0$).

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem units_rank_eq_defect_add_zpRankBelow (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    Units.rank K = defect p K + zpRankBelow p (Module.finrank ℚ K) (unitClosure p K) := by sorry
end Leopoldt
