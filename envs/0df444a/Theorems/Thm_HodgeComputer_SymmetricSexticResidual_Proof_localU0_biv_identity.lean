-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_biv_identity
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localU0_biv_identity
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T10:12:38.306261+00:00
-- url     : https://prove2.me/theorems/21904ed9-4610-49cb-85ee-604b5f897ec4
-- title:
--   Certified bivariate polynomial identity for the $U = 0$ local residue
-- statement:
--   Proves $\operatorname{evalBivK5}(\mathrm{LHS}_{U0,\mathrm{biv}}) = \operatorname{evalBivK5}(\mathrm{RHS}_{U0,\mathrm{biv}})$ in $K_5$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L2651-L2665

import Definitions.Def_HodgeComputerSSR_U0Biv
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localU0_biv_identity :
    SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueU0.LHS_U0_biv =
      SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueU0.RHS_U0_biv := by sorry
