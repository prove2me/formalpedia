-- Prove2me | Theorems.Thm_Leopoldt_leopoldtConjecture_iff_zpRankBelow_eq_units_rank
-- name    : Leopoldt.leopoldtConjecture_iff_zpRankBelow_eq_units_rank
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:14:12.54462+00:00
-- url     : https://prove2.me/theorems/61ebebd1-5692-47e4-97a5-b27e1742871c
-- title:
--   Leopoldt’s conjecture as equality of unit ranks
-- statement:
--   Let $p$ be prime and $K$ a number field. Write $r$ for the Dirichlet rank of the unit group, and $\bar E$ for the closure of its diagonal image in the semilocal units at $p$. Then Leopoldt’s conjecture is equivalent to equality of ranks:
--
--   $$
--   \mathcal D_L(K)=0\quad\Longleftrightarrow\quad \operatorname{rank}_{\mathbb Z_p}(\bar E)=r.
--   $$
--
--   The mission’s bounded rank operation `zpRankBelow` measures the $p$-adic rank of $\bar E$ using continuous embeddings of finite free $\mathbb Z_p$ modules, with the field degree as bound. The established upper bound ensures that defect zero forces equality, while equality immediately gives defect zero. This equivalence is a reusable interface between the defect formulation and a concrete rank goal.
--
--   **Formalization Note** The defect is natural-number subtraction; the rank upper bound is essential to the forward implication.
-- source:
--   Preda Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544v4, Section 1.1, p. 3, definition of the Leopoldt defect as the difference of the integral rank of global units and the p-adic rank of their closure; combined with the established formalized rank upper bound Leopoldt.zpRankBelow_unitClosure_le_units_rank.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem leopoldtConjecture_iff_zpRankBelow_eq_units_rank (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    LeopoldtConjecture p K ↔
      zpRankBelow p (Module.finrank ℚ K) (unitClosure p K) = Units.rank K := by sorry
end Leopoldt
