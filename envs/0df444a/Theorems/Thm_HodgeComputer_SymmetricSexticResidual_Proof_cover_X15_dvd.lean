-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_X15_dvd
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.cover_X15_dvd
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T08:47:10.678629+00:00
-- url     : https://prove2.me/theorems/fba0b4a5-465f-4706-8c0f-3e3aef05a788
-- title:
--   Order-15 vanishing $U^{15} \mid \mathrm{nm}_z$ at $U = 0$
-- statement:
--   Proves $U^{15} \mid \mathrm{nm}_z$ in $K_5[U]$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverAlgebra.lean#L2238-L2705

import Definitions.Def_HodgeComputerSSR_CoverParams
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.cover_X15_dvd :
    (Polynomial.X : Polynomial SymmetricSexticResidual.K5Field.K5) ^ 15 ∣
      SymmetricSexticResidual.CoverAlgebra.k5Params.nm_z := by sorry
