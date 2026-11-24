-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_global_biv_x0
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.global_biv_x0
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T22:34:10.265117+00:00
-- url     : https://prove2.me/theorems/a1a0f5c0-02c8-43e5-b9ea-e3f048864922
-- title:
--   Certified $x^0$-slice vanishing of the global residue cancellation polynomial
-- statement:
--   Proves $\operatorname{evalBivK5}(\operatorname{bivFilterX0}(\mathrm{LHS}_{\mathrm{glob},\mathrm{biv}})) = 0$ in $K_5$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5.lean#L252-L260

import Definitions.Def_HodgeComputerSSR_GlobalBiv
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.global_biv_x0 :
    SymmetricSexticResidual.LocalResidueU0.evalBivK5
      (SymmetricSexticResidual.LocalResidueU0.bivFilterX0
        SymmetricSexticResidual.LocalResidueQ5.LHS_glob_biv) = 0 := by sorry
