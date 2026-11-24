-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_global_residue_cancellation
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.global_residue_cancellation
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T21:56:18.261153+00:00
-- url     : https://prove2.me/theorems/ef74b46e-d840-4582-9525-99c1066b1101
-- title:
--   Exact global residue cancellation identity in $K_5$
-- statement:
--   The local residues at $U = 0$, $U = \infty$, and $Q_5(U) = 0$ cancel the horizontal residual $P_{\mathrm{horiz}, 5}$ identically in $K_5$: $\operatorname{toK5}(P_{\mathrm{horiz}, 5}) = -\operatorname{toK5\_RInf} / L_K^2 - \operatorname{toK5\_RU} - \operatorname{toK5\_RQ5} / L_K^2$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5.lean#L261-L325

import Definitions.Def_HodgeComputerSSR_K5Field
import Definitions.Def_HodgeComputerSSR_VerticalData
import Definitions.Def_HodgeComputerSSR_RUData
import Definitions.Def_HodgeComputerSSR_RInfData
import Definitions.Def_HodgeComputerSSR_RQ5Data
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.global_residue_cancellation :
    SymmetricSexticResidual.K5Field.toK5 SymmetricSexticResidual.VerticalIdentity.P_horiz_5 =
      -SymmetricSexticResidual.LocalResidueU0.toK5_RInf /
          SymmetricSexticResidual.LocalResidueU0.L_K ^ 2 -
        SymmetricSexticResidual.LocalResidueU0.toK5_RU -
        SymmetricSexticResidual.LocalResidueU0.toK5_RQ5 /
          SymmetricSexticResidual.LocalResidueU0.L_K ^ 2 := by sorry
