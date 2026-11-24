-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_vertical_K5_identity
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.vertical_K5_identity
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:44:54.498649+00:00
-- url     : https://prove2.me/theorems/e475b011-88d2-488e-855f-0ba190defb5a
-- title:
--   Exact 5-variable vertical divergence identity in $K_5$
-- statement:
--   The explicit 7-term vertical ansatz $w_V : \operatorname{Fin} 4 \to K_5$ and horizontal residual polynomial $P_{\mathrm{horiz}, 5}$ satisfy the exact identity
--
--   $$2 W_2 H_0^2 \,\operatorname{resDivW}(w_V) + P_{\mathrm{horiz}, 5} = \mathrm{NA}_{Q5} \cdot H_0$$
--
--   in the reduced hypersurface field $K_5$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/VerticalIdentity.lean

import Definitions.Def_HodgeComputerSSR_K5Field
import Definitions.Def_HodgeComputerSSR_VerticalData
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.vertical_K5_identity :
    2 * SymmetricSexticResidual.K5Field.W2_K * SymmetricSexticResidual.K5Field.H0_K ^ 2 *
      SymmetricSexticResidual.K5Field.resDivW SymmetricSexticResidual.VerticalIdentity.w_V +
      SymmetricSexticResidual.K5Field.toK5 SymmetricSexticResidual.VerticalIdentity.P_horiz_5 =
    SymmetricSexticResidual.K5Field.toK5 SymmetricSexticResidual.K5Field.NA_Q5 *
      SymmetricSexticResidual.K5Field.H0_K := by sorry
