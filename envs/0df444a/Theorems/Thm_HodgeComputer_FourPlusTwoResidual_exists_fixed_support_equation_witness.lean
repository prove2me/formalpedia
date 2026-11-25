-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_fixed_support_equation_witness
-- name    : HodgeComputer.FourPlusTwoResidual.exists_fixed_support_equation_witness
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T13:48:27.268036+00:00
-- url     : https://prove2.me/theorems/6c59f326-09e2-4d5e-9b95-461b59047822
-- title:
--   Unconditional affine fixed-support numerator witness for $y^3$
-- statement:
--   **Claim.** There exist a nonzero affine denominator $B\in\mathbb{C}[x,y,z]$, a pole order $n\in\mathbb{N}$, and numerators $N=(N_0,N_1,N_2)$ such that $h\nmid B$ and the cleared fixed-support identity
--
--   $$
--   2\,B\sum_i N_i\partial_i h - 3\,h\Bigl(B\sum_i\partial_i N_i - n\sum_i N_i\partial_i B\Bigr) = 3\,y^3 B^{n+1}
--   $$
--
--   holds, where $h=$ `affineCore` is the dehomogenized four-plus-two core.
--
--   This is the unconditional witness form of dossier Lemma L9 / Discussion #120 (linear numerator recovery on a fixed $H$-coprime swept support). Low-degree Macaulay ansätze are inconsistent, so an explicit shivm-style determinant certificate or a high-degree swept resultant support is expected.
--
--   **Formalization Note.** Dropping the ambient hypothesis of `fixed_support_numerators_of_affine_swept_support`; that parent reduces by ignoring its hypothesis and invoking this witness.
-- source:
--   hodge-computer/sextics Discussion #120; dossier Lemma L9; Prove2Me theorem fixed_support_numerators_of_affine_swept_support (97470f3d)

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.exists_fixed_support_equation_witness :
    ∃ (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧
        ¬(HodgeComputer.FourPlusTwoResidual.affineCore ∣ B) ∧
          HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B n N := by sorry
