-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_E0_irreducible
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.cover_E0_irreducible
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T09:22:06.990339+00:00
-- url     : https://prove2.me/theorems/cc0026d9-8beb-4f23-95ff-eff092e44535
-- title:
--   Irreducibility of the quadratic cover polynomial $E_0(W)$ over $\operatorname{RatFunc}(K_5)$
-- statement:
--   Proves that $E_{0,\mathrm{poly}} = W^2 + b_W(U) W + c_W(U)$ is irreducible over $\operatorname{RatFunc}(K_5)$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverResidue.lean#L261-L490

import Definitions.Def_HodgeComputerSSR_CoverE0
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.cover_E0_irreducible :
    Irreducible SymmetricSexticResidual.CoverResidue.E0_poly := by sorry
