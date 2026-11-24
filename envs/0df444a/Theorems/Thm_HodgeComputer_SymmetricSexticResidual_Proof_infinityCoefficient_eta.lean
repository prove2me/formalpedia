-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_infinityCoefficient_eta
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.infinityCoefficient_eta
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-24T21:55:41.941319+00:00
-- url     : https://prove2.me/theorems/6426e5b3-86b1-4ebe-9a1f-cdcfa46e3427
-- title:
--   Exact coefficient of $\eta$ at $U = \infty$
-- statement:
--   The residue coefficient at infinity of $\eta \in \operatorname{RatFunc}(K_5)$ satisfies $\operatorname{infinityCoefficient}(\eta) = -\operatorname{toK5\_RInf} / L_K^2$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInf.lean#L3086-L3204

import Definitions.Def_HodgeComputerFormal_RationalResidues
import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Definitions.Def_HodgeComputerSSR_RInfData
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.infinityCoefficient_eta :
    CrossedRationalResidue.infinityCoefficient SymmetricSexticResidual.CoverResidue.eta =
      -SymmetricSexticResidual.LocalResidueU0.toK5_RInf /
        SymmetricSexticResidual.LocalResidueU0.L_K ^ 2 := by sorry
