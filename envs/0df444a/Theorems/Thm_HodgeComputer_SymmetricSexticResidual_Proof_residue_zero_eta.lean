-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_residue_zero_eta
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.residue_zero_eta
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T14:53:23.607853+00:00
-- url     : https://prove2.me/theorems/eb8fbf98-22fe-4525-b7a1-9677e64feca1
-- title:
--   Exact local residue of $\eta$ at $U = 0$
-- statement:
--   The residue of the cover 1-form $\eta \in \operatorname{RatFunc}(K_5)$ at $U = 0$ equals `toK5_RU`: $\operatorname{residue}(0, \eta) = \operatorname{toK5\_RU}$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L4061-L4343

import Definitions.Def_HodgeComputerFormal_RationalResidues
import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Definitions.Def_HodgeComputerSSR_RUData
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.residue_zero_eta :
    CrossedRationalResidue.residue 0 SymmetricSexticResidual.CoverResidue.eta =
      SymmetricSexticResidual.LocalResidueU0.toK5_RU := by sorry
