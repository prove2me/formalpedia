-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_X15_W2_val
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.cover_X15_W2_val
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T08:39:31.937588+00:00
-- url     : https://prove2.me/theorems/2f5b3559-8d4e-4d87-8ce1-9724ec8f7c98
-- title:
--   Order-2 vanishing of $\mathrm{res}_z$ on Branch 2 ($W_{2,0}$) at $U = 0$
-- statement:
--   Proves $\operatorname{HasValGe}(2, \operatorname{evalAt}(W_{2,0}, \mathrm{res}_z))$ along the nonvanishing $O(1)$ branch $W_{2,0}$ above $U = 0$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverAlgebra.lean#L2531-L2705

import Definitions.Def_HodgeComputerSSR_CoverParams
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.cover_X15_W2_val :
    QuadraticCovers.HasValGe 2
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W2_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.res_z)) := by sorry
