-- Prove2me | Theorems.Thm_Leopoldt_defect_eq_zero_cyclotomicField
-- name    : Leopoldt.defect_eq_zero_cyclotomicField
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-09T15:35:31.695637+00:00
-- url     : https://prove2.me/theorems/1da49dbf-2534-4729-99f2-397e126c2f6a
-- title:
--   Brumer's theorem for cyclotomic fields
-- statement:
--   Let $p$ be a prime and $n$ a natural number, and let $\mathbb{Q}(\zeta_n)$ be the $n$-th cyclotomic field, the splitting field of the $n$-th cyclotomic polynomial over $\mathbb{Q}$. Then the Leopoldt defect vanishes:
--
--   $$\mathcal{D}_L(\mathbb{Q}(\zeta_n)) \;=\; 0 .$$
--
--   This is the cyclotomic case of Brumer's theorem. It is the case from which the general abelian one follows: by the Kronecker-Weber theorem every finite abelian extension of $\mathbb{Q}$ is contained in some $\mathbb{Q}(\zeta_n)$, and a vanishing defect is inherited by subfields, which is the contrapositive of Remark 1.A of the mission source.
--
--   It is also the case in which the Diophantine argument has explicit units to work with. For a general number field nothing produces units with a controlled Galois structure, which is where the transcendence route stalls; for a cyclotomic field the cyclotomic units do, and the $p$-adic regulator can be written through characters as a product of linear forms in $p$-adic logarithms of algebraic numbers with algebraic coefficients, to which Brumer's $p$-adic analogue of Baker's theorem on linear forms in logarithms applies.
--
--   **Formalization note.** `CyclotomicField n ℚ` is Mathlib's splitting field of the $n$-th cyclotomic polynomial over $\mathbb{Q}$, that is $\mathbb{Q}(\zeta_n)$. No positivity hypothesis on $n$ is imposed: for $n = 0$ the cyclotomic polynomial is constant and the field is $\mathbb{Q}$ itself, where the statement holds because Dirichlet's unit rank is $0$; and $\mathbb{Q}(\zeta_1) = \mathbb{Q}(\zeta_2) = \mathbb{Q}$ likewise. No hypothesis relates $p$ to $n$.
-- source:
--   The case K = Q(zeta_n) of Brumer's theorem, whose attribution in the mission source is Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544 (v4, 17 Feb 2016), Section 1 (Introduction), p. 2: "Leopoldt suggested in his seminal paper that the p-adic regulator of abelian extensions of Q never vanishes. This fact could be proved by Brumer in 1967, using a plan of Ax, as soon as Baker had proved his archimedean version of the approximation Theorem for linear forms in logarithms: it remained to adapt Baker's proof to the p-adic topology." Original: A. Brumer, On the units of algebraic number fields, Mathematika 14 (1967), 121-124, https://doi.org/10.1112/S0025579300003703; reduction in J. Ax, On the units of an algebraic number field, Illinois J. Math. 9 (1965), 584-589, https://doi.org/10.1215/ijm/1256059299. The defect used is the one defined in Section 1.1, p. 3 of the mission source.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_eq_zero_cyclotomicField (p : ℕ) [Fact p.Prime] (n : ℕ) :
    defect p (CyclotomicField n ℚ) = 0 := by sorry
end Leopoldt
