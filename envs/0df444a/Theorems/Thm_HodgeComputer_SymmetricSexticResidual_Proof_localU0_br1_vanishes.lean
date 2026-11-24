-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_br1_vanishes
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localU0_br1_vanishes
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T12:25:15.70159+00:00
-- url     : https://prove2.me/theorems/7247ae69-de82-40db-8694-e833a09005c0
-- title:
--   Vanishing of the $U = 0$ Branch-1 residue $(\operatorname{br}_{1,0}(\eta_{A_C}))_{-1} = 0$
-- statement:
--   Along the regular $O(U^2)$ branch `br1_0` above $U = 0$, the $U^{-1}$-coefficient of $\eta_{A_C}$ vanishes.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L1841-L2250

import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Definitions.Def_HodgeComputerSSR_BranchHelpers
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localU0_br1_vanishes :
    (SymmetricSexticResidual.LocalResidueU0.br1_0 SymmetricSexticResidual.CoverResidue.eta_AC).coeff (-1) = 0 := by sorry
