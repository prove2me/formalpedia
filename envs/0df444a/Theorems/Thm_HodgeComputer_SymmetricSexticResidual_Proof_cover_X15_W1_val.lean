-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_X15_W1_val
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.cover_X15_W1_val
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T08:30:57.582594+00:00
-- url     : https://prove2.me/theorems/905fb697-d9ce-479e-8909-5ad7412fa38b
-- title:
--   Order-13 vanishing of $\mathrm{res}_z$ on Branch 1 ($W_{1,0}$) at $U = 0$
-- statement:
--   Proves $\operatorname{HasValGe}(13, \operatorname{evalAt}(W_{1,0}, \mathrm{res}_z))$ along the regular $O(U^2)$ branch $W_{1,0}$ above $U = 0$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverAlgebra.lean#L2238-L2530

import Definitions.Def_HodgeComputerSSR_CoverParams
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.cover_X15_W1_val :
    QuadraticCovers.HasValGe 13
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W1_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.res_z)) := by sorry
