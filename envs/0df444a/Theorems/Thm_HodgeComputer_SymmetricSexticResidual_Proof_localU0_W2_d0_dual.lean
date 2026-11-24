-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_W2_d0_dual
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_d0_dual
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T11:25:15.356256+00:00
-- url     : https://prove2.me/theorems/a8092f71-a61c-4bc1-8410-b4cdb2f8945e
-- title:
--   Exact leading $U^1$ coefficient of $d_{0,z}$ on Branch 2 ($W_{2,0}$) at $U = 0$
-- statement:
--   Along $W_{2,0}$ above $U = 0$, $d_{0,z}(W_{2,0})$ vanishes at $U = 0$ with exact order-$1$ leading coefficient $d_{0,1}$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L726-L810

import Definitions.Def_HodgeComputerSSR_BranchHelpers
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_d0_dual :
    let A := 5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K
    let B := SymmetricSexticResidual.K5Field.T_K - 3
    let w0 := -(SymmetricSexticResidual.CoverAlgebra.k5Params.Bv0 *
      SymmetricSexticResidual.CoverAlgebra.k5Params.Av0_inv)
    let z2 := w0 * SymmetricSexticResidual.K5Field.S_K / B
    let q2_0 := (15625 / 59049 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.S_K * A ^ 4
    let d0_1 := (-59604644775390625 / 103769130575703096 : SymmetricSexticResidual.K5Field.K5) *
      (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K +
        77 * SymmetricSexticResidual.K5Field.T_K - 189) *
      SymmetricSexticResidual.K5Field.S_K ^ 8 * (-A) ^ 17 / B ^ 12
    QuadraticCovers.ValLead 1
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W2_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.d0_z)) d0_1 ∧
    QuadraticCovers.ValLead 0
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W2_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.d2_2)) q2_0 ∧
    QuadraticCovers.ValLead 0
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W2_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.d2_1)) (-2 * q2_0 * z2) ∧
    QuadraticCovers.ValLead 0
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W2_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.d2_0)) (q2_0 * z2 ^ 2) := by sorry
