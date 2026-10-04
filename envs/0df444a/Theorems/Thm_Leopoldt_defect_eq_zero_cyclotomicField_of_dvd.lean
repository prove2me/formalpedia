-- Prove2me | Theorems.Thm_Leopoldt_defect_eq_zero_cyclotomicField_of_dvd
-- name    : Leopoldt.defect_eq_zero_cyclotomicField_of_dvd
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:40:53.465448+00:00
-- url     : https://prove2.me/theorems/a8d9f9f4-cf2d-4409-94ba-91e785c692bf
-- title:
--   Brumer's theorem for $\mathbb{Q}(\zeta_m)$ with $4p \mid m$
-- statement:
--   Let $p$ be a prime and let $m \ge 1$ be a natural number divisible by $4p$, so that the $m$-th cyclotomic field $\mathbb{K} = \mathbb{Q}(\zeta_m)$ contains the $p$-th roots of unity $\mu_p$ and the fourth roots of unity $\mu_4$ (for $p = 2$: the eighth roots of unity). Then the Leopoldt defect of $\mathbb{K}$ at $p$ vanishes:
--
--   $$
--   \mathcal{D}_L\big(\mathbb{Q}(\zeta_m)\big) \;=\; 0 \qquad (4p \mid m,\ m > 0).
--   $$
--
--   Here $\mathcal{D}_L(\mathbb{K}) = \operatorname{rank}_{\mathbb{Z}} E(\mathbb{K}) - \operatorname{rank}_{\mathbb{Z}_p} \overline{E}(\mathbb{K})$ is the defect of Section 1.1 of the mission source, $E(\mathbb{K}) = \mathcal{O}_{\mathbb{K}}^\times$ being the global units and $\overline{E}(\mathbb{K})$ the closure of their diagonal image in the product $\prod_{\wp \mid p} \mathcal{O}_\wp^\times$ of the local unit groups at the primes above $p$.
--
--   This is Brumer's theorem (Leopoldt's conjecture for abelian number fields) for the cofinal family of cyclotomic fields whose level is divisible by $4p$. Such a field is Galois over $\mathbb{Q}$, CM, and contains the $p$-th roots of unity, as the working base field of the mission source does; the additional requirement $4 \mid m$ is a convenience normalisation not taken from the source. By Remark 1.A of the source (a positive defect is inherited by finite extensions), Leopoldt's conjecture for $\mathbb{Q}(\zeta_m)$ implies it for every subfield, in particular for every $\mathbb{Q}(\zeta_n)$ with $n \mid m$; since every $n \ge 1$ divides $4pn$, this family determines the conjecture for all cyclotomic fields.
--
--   **Formalization Note.** `CyclotomicField m ℚ` is Mathlib's splitting field of the $m$-th cyclotomic polynomial over $\mathbb{Q}$. The hypothesis $0 < m$ excludes the degenerate level $m = 0$ (divisible by every integer, with `CyclotomicField 0 ℚ` equal to $\mathbb{Q}$); the statement would remain true there, but the exclusion keeps the family equal to the cyclotomic fields containing $\mu_{4p}$.
-- source:
--   Brumer's theorem (Leopoldt's conjecture for abelian extensions of Q), as attributed in the mission source: Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544 (v4, 17 Feb 2016), Section 1 (Introduction), p. 2: "Leopoldt suggested in his seminal paper that the p-adic regulator of abelian extensions of Q never vanishes. This fact could be proved by Brumer in 1967, using a plan of Ax". Original: A. Brumer, On the units of algebraic number fields, Mathematika 14 (1967), 121-124, https://doi.org/10.1112/S0025579300003703; see also Washington, Introduction to Cyclotomic Fields, Corollary 5.32. The requirement p | m follows the source's normalisation of the working base field (Section 1.3, Remark 1 part A, p. 5, which permits passing to finite extensions, and the opening of Section 2 (Auxiliary constructions): the base field's 'choice is still arbitrary, except for the fact that it should possibly be galois and contain the p-th roots of unity'; Section 2.2 (The working base field and a split Thaine shift): K_{-1} := K_start^{(n)}[zeta_p]). The defect is the one of Section 1.1, p. 3. The extra factor 4 (so that i lies in the field) is a convenience normalisation of this formalization, not taken from the source; the source also assumes p odd, whereas this statement includes p = 2.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_eq_zero_cyclotomicField_of_dvd (p : ℕ) [Fact p.Prime] (m : ℕ)
    (hm : 0 < m) (hpm : 4 * p ∣ m) :
    defect p (CyclotomicField m ℚ) = 0 := by sorry
end Leopoldt
