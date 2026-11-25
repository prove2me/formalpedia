-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_fixed_support_numerators_of_affine_swept_support
-- name    : HodgeComputer.FourPlusTwoResidual.fixed_support_numerators_of_affine_swept_support
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T11:57:21.502458+00:00
-- url     : https://prove2.me/theorems/97470f3d-10c9-50ed-b566-53c00fc88312
-- title:
--   Affine swept support admits a linear fixed-support numerator solution
-- statement:
--   **Claim.** If there exists a nonzero affine $B$ with $h\nmid B$, then there exist such a $B$, a pole order $n$, and numerators $N_0,N_1,N_2$ satisfying `FixedSupportEquation B n N`.
--
--   For fixed admissible $B$, the cleared fixed-support identity is linear in the $N_i$ (dossier Lemma L9). The geometric content is that some $H$-coprime swept support makes that linear system solvable for the source $y^3$.
--
--   **Formalization Note.** Second half of the resultant→fixed-support glue; conclusion matches `exists_swept_fixed_support_of_core_resultant`.
-- source:
--   Discussion #120 linear numerator recovery; shivm witness-and-determinant methodology; dossier Lemma L9, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.fixed_support_numerators_of_affine_swept_support
    (hB : ∃ (B : MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧ ¬(HodgeComputer.FourPlusTwoResidual.affineCore ∣ B)) :
    ∃ (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧
        ¬(HodgeComputer.FourPlusTwoResidual.affineCore ∣ B) ∧
          HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B n N := by sorry
