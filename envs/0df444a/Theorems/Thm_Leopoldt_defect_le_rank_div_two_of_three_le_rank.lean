-- Prove2me | Theorems.Thm_Leopoldt_defect_le_rank_div_two_of_three_le_rank
-- name    : Leopoldt.defect_le_rank_div_two_of_three_le_rank
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T02:07:14.195989+00:00
-- url     : https://prove2.me/theorems/7409d2ac-6450-4ad5-aca1-7231e7466152
-- title:
--   Waldschmidt's bound $\mathcal{D}_L(\mathbb{K}) \le r/2$ for unit rank $r \ge 3$
-- statement:
--   Let $p$ be a prime and $\mathbb{K}$ a number field whose unit group $E = \mathcal{O}(\mathbb{K})^\times$ has Dirichlet rank $r = \mathbb{Z}\text{-rk}(E) \ge 3$. With $U = \prod_{\wp \mid p}\mathcal{O}_\wp^\times$ the semilocal units at $p$, $\iota : E \to U$ the diagonal embedding and $\bar E = \bigcap_{n>0}\iota(E)\cdot U^{p^n}$ the $p$-adic closure of the units, the Leopoldt defect satisfies
--
--   $$
--   \mathcal{D}_L(\mathbb{K}) \;=\; r - \mathbb{Z}_p\text{-rk}(\bar{E}) \;\le\; \frac{r}{2}.
--   $$
--
--   This is Waldschmidt's theorem restricted to unit rank at least $3$, which is exactly the range in which it goes beyond the elementary bound $\mathcal{D}_L(\mathbb{K}) \le r - 1$ (a unit of infinite order generates a copy of $\mathbb{Z}_p$ in $\bar E$). Its proof is transcendence theory: a $p$-adic lower bound for the rank of matrices of $p$-adic logarithms of algebraic numbers, applied to the logarithms of the conjugates of a system of fundamental units. Together with the elementary bound it gives Waldschmidt's inequality for every number field.
--
--   **Formalization Note** The right-hand side is $\lfloor r/2 \rfloor$ (division in $\mathbb{N}$), matching the milestone `Leopoldt.defect_le_rank_div_two`, of which this is the case $r \ge 3$.
-- source:
--   Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, Section 1.2 (Historical notes), p. 4, quoting M. Waldschmidt, Transcendance et exponentielles en plusieurs variables, Invent. Math. 63 (1981), 97–127: 'if r is the Z-rank of the units in the field K, then the Leopoldt defect satisfies D_L(K) ≤ r/2'. Restricted here to r ≥ 3.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_le_rank_div_two_of_three_le_rank (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] (hr : 3 ≤ Units.rank K) :
    defect p K ≤ Units.rank K / 2 := by sorry
end Leopoldt
