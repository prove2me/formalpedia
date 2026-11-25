-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_geometric_projected_swept_resultant
-- name    : HodgeComputer.FourPlusTwoResidual.exists_geometric_projected_swept_resultant
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-25T13:48:24.890313+00:00
-- url     : https://prove2.me/theorems/32199c1f-705b-41d8-929f-941fd7479603
-- title:
--   Non-unit geometric projected swept resultant coprime to $H$ and $\sigma_{AB}$
-- statement:
--   **Claim (optional strengthening).** There exists a **non-unit** polynomial $R\in\mathbb{C}[x_0,x_1,y_0,y_1]$ with $R\ne 0$, $H\nmid R$, and $H\nmid \sigma_{AB}(R)$, where $H=$ `core` and $\sigma_{AB}=$ `flipAB`.
--
--   This strengthens the constant witness $R=1$ for `exists_projected_swept_sign_translate_denominator` toward a genuine projected swept-surface resultant (Discussion #120: characteristic-zero projected swept surface has degree at least $361$). A full geometric version would additionally place $R$ in the contact/sweep elimination ideal; the present statement records the minimal non-unit strengthening that excludes constants.
--
--   **Formalization Note.** Optional child suggested alongside fixed-support numerator recovery; not required for the parent sketch.
-- source:
--   hodge-computer/sextics Discussion #120 (projected swept surface / resultant); optional strengthening of exists_projected_swept_sign_translate_denominator

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.exists_geometric_projected_swept_resultant :
    ∃ (R : MvPolynomial (Fin 4) ℂ),
      R ≠ 0 ∧
        ¬ IsUnit R ∧
          ¬(HodgeComputer.FourPlusTwoResidual.core ∣ R) ∧
            ¬(HodgeComputer.FourPlusTwoResidual.core ∣
                HodgeComputer.FourPlusTwoResidual.flipAB R) := by sorry
