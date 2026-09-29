-- Prove2me | Theorems.Thm_Leopoldt_defect_eq_zero_cyclotomicField_of_four_lt_totient
-- name    : Leopoldt.defect_eq_zero_cyclotomicField_of_four_lt_totient
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T02:17:15.771439+00:00
-- url     : https://prove2.me/theorems/f79d3e92-42f5-4ce2-897b-9c2e770d93c0
-- title:
--   Brumer's theorem for $\mathbb{Q}(\zeta_n)$ with $\varphi(n) > 4$
-- statement:
--   Let $p$ be a prime and let $n$ be a natural number with $\varphi(n) > 4$, where $\varphi$ is Euler's totient function, so that $\mathbb{Q}(\zeta_n)$ is a totally complex field of degree $\varphi(n) \ge 6$ and unit rank $\varphi(n)/2 - 1 \ge 2$. Then the Leopoldt defect of the $n$-th cyclotomic field vanishes:
--
--   $$
--   \mathcal{D}_L\big(\mathbb{Q}(\zeta_n)\big) \;=\; 0 .
--   $$
--
--   Here $\mathcal{D}_L(K) = \operatorname{rank}_{\mathbb{Z}} \mathcal{O}_K^\times - \operatorname{rank}_{\mathbb{Z}_p} \overline{E}$ is the defect of Section 1.1 of the mission source, $\overline{E}$ being the closure of the diagonal image of the global units in the product of the local unit groups at the primes above $p$.
--
--   This is Brumer's theorem for cyclotomic fields in the range where it is not elementary. When $\varphi(n) \le 4$ the unit rank is at most $1$ and the vanishing follows from the general bound $\mathcal{D}_L(K) \le \operatorname{rank} \mathcal{O}_K^\times - 1$; for $\varphi(n) > 4$ one needs Brumer's $p$-adic analogue of Baker's theorem on linear forms in logarithms, applied to the cyclotomic units via the character decomposition of the $p$-adic regulator.
--
--   **Formalization Note.** `CyclotomicField n ℚ` is Mathlib's splitting field of the $n$-th cyclotomic polynomial over $\mathbb{Q}$. The hypothesis $4 < \varphi(n)$ excludes exactly the fields $\mathbb{Q}$ ($n = 0,1,2$), $\mathbb{Q}(\zeta_3)$, $\mathbb{Q}(i)$, $\mathbb{Q}(\zeta_5)$, $\mathbb{Q}(\zeta_8)$ and $\mathbb{Q}(\zeta_{12})$ (together with $n = 6, 10$, which give the same fields). No hypothesis relates $p$ to $n$.
-- source:
--   Brumer's theorem (the case K = Q(zeta_n) with phi(n) > 4), as attributed in the mission source: Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544 (v4, 17 Feb 2016), Section 1 (Introduction), p. 2: "Leopoldt suggested in his seminal paper that the p-adic regulator of abelian extensions of Q never vanishes. This fact could be proved by Brumer in 1967 ...". Original: A. Brumer, On the units of algebraic number fields, Mathematika 14 (1967), 121-124, https://doi.org/10.1112/S0025579300003703; see also Washington, Introduction to Cyclotomic Fields, Corollary 5.32 and Section 5.5. The defect is the one of Section 1.1, p. 3 of the mission source.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_eq_zero_cyclotomicField_of_four_lt_totient (p : ℕ) [Fact p.Prime] (n : ℕ)
    (hn : 4 < n.totient) :
    defect p (CyclotomicField n ℚ) = 0 := by sorry
end Leopoldt
