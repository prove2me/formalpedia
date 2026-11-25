-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_fixedSupport_of_denominator_free_system
-- name    : HodgeComputer.FourPlusTwoResidual.fixedSupport_of_denominator_free_system
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-25T16:27:53.128892+00:00
-- url     : https://prove2.me/theorems/f870ef6e-edae-5778-9213-ae23c49a77fb
-- title:
--   The denominator-free numerator system yields a fixed-support solution at $n = 0$
-- statement:
--   **The denominator-free system is sufficient, not only necessary.** Write
--   $h(x,y,z) = 1 + \tfrac57 x + \tfrac57 xyz + \tfrac{10}7 x^5 + \tfrac{10}7 x y^3 z + x^6 + y^6 + \tfrac57 y^5 z + \tfrac{15}7 y z^5 + z^6$
--   for the affine four-plus-two core, and for a denominator $B \in \mathbb{C}[x,y,z]$ and a
--   numerator triple $N = (N_0,N_1,N_2)$ consider the cleared affine numerator system
--
--   $$
--   2 B \sum_i N_i \partial_i h - 3 h\Bigl(B \sum_i \partial_i N_i - n \sum_i N_i \partial_i B\Bigr) = 3 y^3 B^{n+1}.
--   $$
--
--   **Theorem.** If the denominator-free polynomial system
--
--   $$
--   2 \sum_i N_i \partial_i h - 3 h \sum_i \partial_i N_i = 3 y^3
--   $$
--
--   holds for a triple $N$, then the cleared system above holds with exponent $n = 0$ and with
--   **any** denominator $B$; that is, $\mathrm{FixedSupportEquation}\; B\; 0\; N$ holds for
--   every $B \in \mathbb{C}[x,y,z]$.
--
--   **Proof.** At $n = 0$ the term $n \sum_i N_i \partial_i B$ vanishes, and every remaining
--   term on the left of the cleared system carries one explicit factor $B$:
--   the left-hand side is $B\bigl(2 \sum_i N_i \partial_i h - 3 h \sum_i \partial_i N_i\bigr)$
--   while the right-hand side is $3 y^3 B$. Distributing the product and rewriting
--   $B^{0+1} = B$, the cleared system becomes $B\,X = B\,(3y^3)$ with
--   $X = 2 \sum_i N_i \partial_i h - 3 h \sum_i \partial_i N_i$; the hypothesis is $X = 3 y^3$,
--   so both sides agree for every $B$. $\square$
--
--   Together with the companion statement
--   `fixedSupport_eq_of_n_eq_zero` — which reads the same cleared system back out of
--   $\mathrm{FixedSupportEquation}\; B\; 0\; N$ for $B \neq 0$ — the exponent-zero branch is
--   an **equivalence** between two statements that do not mention the denominator at all.
--
--   **Consequences for the four-plus-two residual mission.**
--
--   - The exponent-zero branch is *constructive*: any polynomial solution of the
--     denominator-free system produces a fixed-support solution at $n = 0$, and one may then
--     pick an admissible denominator such as the one furnished by
--     `exists_admissible_affine_denominator`, which satisfies $B \neq 0$ and
--     $\neg(\mathrm{affineCore} \mid B)$. So on this branch the coprimality requirement is
--     free.
--   - Conversely, no admissible denominator can *create* a solution: the exponent-zero branch
--     is exactly the denominator-free system, and the exhaustive exact search over 771
--     candidate denominators with numerator degrees up to 10 finds no solution of it (the
--     corresponding linear systems are certified inconsistent over $\mathbb{F}_{65521}$,
--     which certifies inconsistency over $\mathbb{Q}$).
--   - The live content of `fixed_support_numerators_of_affine_swept_support` therefore lies in
--     the branch $n \geq 1$, where the denominator $B$ is genuinely present: the rational
--     numerator $q_i = N_i / B^{n}$ is then a rational solution of the affine core equation
--     with a pole divisor that must not contain the divisor of $h$.
-- source:
--   Four-plus-two residual mission, fixed-support branch: companion of fixedSupport_eq_of_n_eq_zero (proved, this mission); the two statements form the equivalence between the exponent-zero cleared system and the denominator-free numerator system; exact search certificates over F_65521 in the mission workspace

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

open MvPolynomial
open scoped BigOperators

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.fixedSupport_of_denominator_free_system :
    ∀ (B : MvPolynomial (Fin 3) ℂ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      2 * (∑ i, N i * pderiv i HodgeComputer.FourPlusTwoResidual.affineCore) -
          3 * HodgeComputer.FourPlusTwoResidual.affineCore * (∑ i, pderiv i (N i)) =
        3 * X 1 ^ 3 →
        HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B 0 N := by sorry
