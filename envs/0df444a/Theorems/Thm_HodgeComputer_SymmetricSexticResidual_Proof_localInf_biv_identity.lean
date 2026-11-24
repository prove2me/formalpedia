-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_biv_identity
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_identity
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T17:54:59.285774+00:00
-- url     : https://prove2.me/theorems/2f72e5ea-1c23-4634-ac23-2d7ebcac7c15
-- title:
--   Certified bivariate polynomial identity for the $U = \infty$ local residue
-- statement:
--   Proves $\operatorname{evalBivK5}(\mathrm{LHS}_{U\infty,\mathrm{biv}}) = \operatorname{evalBivK5}(\mathrm{RHS}_{U\infty,\mathrm{biv}})$ in $K_5$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInf.lean#L1515-L1518

import Definitions.Def_HodgeComputerSSR_LocalInfBivId
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_identity :
    SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.LHS_Uinf_biv =
      SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.RHS_Uinf_biv := by sorry
