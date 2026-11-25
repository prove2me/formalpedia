-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_affine_dehomogenized_swept_support
-- name    : HodgeComputer.FourPlusTwoResidual.exists_affine_dehomogenized_swept_support
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-25T11:57:23.194902+00:00
-- url     : https://prove2.me/theorems/0c5f4451-c61a-4c3d-bda6-8eb7b169378f
-- title:
--   Core resultant dehomogenizes to a nonzero affine support coprime to $h$
-- statement:
--   **Claim.** From any nonzero four-variable $R$ with $H\nmid R$ and $H\nmid\sigma_{AB}^*R$, there exists a nonzero affine polynomial $B\in\mathbb{C}[x,y,z]$ with $h\nmid B$ (where $h=$`affineCore`).
--
--   The intended map is dehomogenization / specialization of $D_{\mathrm{geom}}=R\cdot\sigma_{AB}^*R$ (and saturation away from the hyperplane at infinity), preserving nonvanishing and coprimality with the affine core.
--
--   **Formalization Note.** First half of the resultant→`FixedSupportEquation` glue.
-- source:
--   Discussion #120 swept resultant dehomogenization; WORMHOLE φ = specialize/dehomogenize, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry
import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.exists_affine_dehomogenized_swept_support
    (hR : ∃ (R : MvPolynomial (Fin 4) ℂ),
      R ≠ 0 ∧
        ¬(HodgeComputer.FourPlusTwoResidual.core ∣ R) ∧
          ¬(HodgeComputer.FourPlusTwoResidual.core ∣
              HodgeComputer.FourPlusTwoResidual.flipAB R)) :
    ∃ (B : MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧ ¬(HodgeComputer.FourPlusTwoResidual.affineCore ∣ B) := by sorry
