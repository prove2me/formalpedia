-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_fixedSupport_eq_of_n_eq_zero
-- name    : HodgeComputer.FourPlusTwoResidual.fixedSupport_eq_of_n_eq_zero
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-25T15:49:31.642524+00:00
-- url     : https://prove2.me/theorems/69f04b2f-9df3-5675-a19b-00375c92bb59
-- title:
--   The exponent-zero fixed-support branch is denominator-free
-- statement:
--   **The exponent-zero branch of the cleared affine numerator system is denominator-free.**
--
--   The cleared fixed-support system for the affine chart, with $h = \mathrm{affineCore}$ and $q_i = N_i / B^n$, is
--
--   $$
--   2 B\,(N \cdot \nabla h) - 3 h\bigl(B\,\mathrm{div}\,N - n\,(N \cdot \nabla B)\bigr) = 3 y^3 B^{n+1}.
--   $$
--
--   For $n = 0$ the term $n (N \cdot \nabla B)$ vanishes, and every remaining term on the left carries an explicit factor $B$: the left-hand side is $B\,(2 (N \cdot \nabla h) - 3 h\,\mathrm{div}\,N)$ while the right-hand side is $3 y^3 B$. Hence, for a nonzero denominator $B$, the factor $B$ cancels and the equation reduces to the **denominator-independent** polynomial system
--
--   $$
--   2\,(N \cdot \nabla h) - 3 h\,\mathrm{div}\,N = 3 y^3 .
--   $$
--
--   **Theorem.** If $B \neq 0$ and $\mathrm{FixedSupportEquation}\; B\; 0\; N$ holds, then $2 (N \cdot \nabla h) - 3 h\, \mathrm{div}\, N = 3 y^3$.
--
--   Consequences for the four-plus-two residual mission: the choice of the swept-support denominator carries no information on the exponent-zero branch, so an admissible denominator alone — such as the one furnished by `exists_admissible_affine_denominator` — cannot be turned into a fixed-support numerator solution on that branch. Any solution on the exponent-zero branch must already solve the fixed polynomial numerator system, independently of the coprimeness of $B$ to $h$.
-- source:
--   Discussion #120 linear numerator recovery; dossier Lemma L9, https://github.com/hodge-computer/sextics/discussions/120; shivm witness-and-determinant methodology (denominator-independent witness isolation)

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

open MvPolynomial
open scoped BigOperators

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.fixedSupport_eq_of_n_eq_zero
    (B : MvPolynomial (Fin 3) ℂ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ)
    (hB : B ≠ 0)
    (h : HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B 0 N) :
    2 * (∑ i, N i * pderiv i HodgeComputer.FourPlusTwoResidual.affineCore) -
        3 * HodgeComputer.FourPlusTwoResidual.affineCore *
          (∑ i, pderiv i (N i)) =
      3 * X 1 ^ 3 := by sorry
