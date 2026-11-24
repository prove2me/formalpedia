-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_br2_vanishes
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localInf_br2_vanishes
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T19:03:14.838172+00:00
-- url     : https://prove2.me/theorems/d86728b5-09f9-442d-a607-2e1bb0198686
-- title:
--   Vanishing of the $U = \infty$ Branch-2 residue $(\operatorname{br}_{2,\infty}(\eta_{A_C}))_{1} = 0$
-- statement:
--   Along the $O(t^{-2})$ branch `br2_inf` above $U = \infty$, the $t^1$-coefficient of $\eta_{A_C}$ vanishes.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInf.lean#L875-L1289

import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Definitions.Def_HodgeComputerSSR_LocalInfCore
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localInf_br2_vanishes :
    (SymmetricSexticResidual.LocalResidueInf.br2_inf SymmetricSexticResidual.CoverResidue.eta_AC).coeff 1 = 0 := by sorry
