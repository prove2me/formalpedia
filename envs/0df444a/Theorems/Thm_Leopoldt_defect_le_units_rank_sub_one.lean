-- Prove2me | Theorems.Thm_Leopoldt_defect_le_units_rank_sub_one
-- name    : Leopoldt.defect_le_units_rank_sub_one
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:07:05.956386+00:00
-- url     : https://prove2.me/theorems/02546c14-1e93-47e7-8347-99cecc127341
-- title:
--   The Leopoldt defect is at most $\mathbb{Z}\text{-rk}(E) - 1$
-- statement:
--   Let $p$ be a prime and $\mathbb{K}$ a number field, with unit group $E = \mathcal{O}(\mathbb{K})^\times$ of Dirichlet rank $r = \mathbb{Z}\text{-rk}(E) = r_1 + r_2 - 1$. Let $U = \prod_{\wp \mid p} \mathcal{O}_\wp^\times$ be the semilocal units at $p$, $\iota : E \to U$ the diagonal embedding, and $\bar{E} = \bigcap_{n>0} \iota(E)\cdot U^{p^n}$ the $p$-adic closure of the global units. Then the Leopoldt defect satisfies
--
--   $$
--   \mathcal{D}_L(\mathbb{K}) \;=\; r - \mathbb{Z}_p\text{-rk}(\bar{E}) \;\le\; r - 1 .
--   $$
--
--   Equivalently, whenever $r \ge 1$ the $p$-adic closure $\bar{E}$ has $\mathbb{Z}_p$-rank at least $1$: a single unit of infinite order already generates a copy of $\mathbb{Z}_p$ inside $\bar{E}$, because $p$-adic completion cannot turn a unit of infinite order into a torsion element.
--
--   This is the trivial lower bound on the $p$-adic rank of the units, the first case of the inequality $\mathbb{Z}_p\text{-rk}(\bar E) \ge r/2$ of Waldschmidt. Since $r - 1 \le \lfloor r/2 \rfloor$ exactly when $r \le 2$, it proves Waldschmidt's bound, and hence also settles Leopoldt's conjecture ($\mathcal{D}_L(\mathbb{K}) = 0$), for every number field of unit rank $r \le 1$ (real quadratic fields, complex cubic fields, CM quartic fields, …), and gives $\mathcal{D}_L(\mathbb{K}) \le 1$ when $r = 2$.
--
--   **Formalization Note** Subtraction is in $\mathbb{N}$ and truncates; for $r = 0$ the statement reads $\mathcal{D}_L(\mathbb{K}) \le 0$, which is the (already proved) rank-zero case.
-- source:
--   Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, Section 1.2 (Historical notes), p. 4: the bound D_L(K) ≤ r/2 of Waldschmidt (Invent. Math. 63 (1981), 97–127); this is its elementary r ≤ 2 case (Z_p-rank of the closure of a unit of infinite order is 1).

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_le_units_rank_sub_one (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    defect p K ≤ Units.rank K - 1 := by sorry
end Leopoldt
