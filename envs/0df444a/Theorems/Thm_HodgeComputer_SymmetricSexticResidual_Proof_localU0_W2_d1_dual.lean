-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_W2_d1_dual
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_d1_dual
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-24T11:03:45.558514+00:00
-- url     : https://prove2.me/theorems/8596655a-4181-4a7e-8138-52b7716c4e32
-- title:
--   Exact leading $U^1$ coefficient of $d_{1,z}$ on Branch 2 ($W_{2,0}$) at $U = 0$
-- statement:
--   Along $W_{2,0}$ above $U = 0$, $d_{1,z}(W_{2,0})$ vanishes at $U = 0$ with exact order-$1$ leading coefficient $d_{1,1}$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L394-L725

import Definitions.Def_HodgeComputerSSR_BranchHelpers
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_d1_dual :
    let A := 5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K
    let B := SymmetricSexticResidual.K5Field.T_K - 3
    let d1_1 := (-2384185791015625 / 25942282643925774 : SymmetricSexticResidual.K5Field.K5) *
      (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K +
        77 * SymmetricSexticResidual.K5Field.T_K - 210) *
      SymmetricSexticResidual.K5Field.S_K ^ 6 * (-A) ^ 15 / B ^ 8
    QuadraticCovers.ValLead 1
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W2_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.d1_z)) d1_1 := by sorry
