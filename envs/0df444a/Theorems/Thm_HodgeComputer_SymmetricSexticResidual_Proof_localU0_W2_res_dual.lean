-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_W2_res_dual
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_res_dual
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T11:35:30.998173+00:00
-- url     : https://prove2.me/theorems/4cf80347-bd67-4e87-99a6-4a7a0c7728e6
-- title:
--   Exact leading valuations of $\mathrm{res}_z$ on both $U = 0$ branches ($W_{2,0}$ and $W_{1,0}$)
-- statement:
--   Proves that $\mathrm{res}_z(W_{2,0})$ has exact order $2$ with explicit nonzero leading coefficient $c_d^2 / q_{2,0}$, and $\mathrm{res}_z(W_{1,0})$ has valuation $\ge 13$ with nonzero $U^{13}$-coefficient.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L811-L893

import Definitions.Def_HodgeComputerSSR_BranchHelpers
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localU0_W2_res_dual :
    let A := 5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K
    let B := SymmetricSexticResidual.K5Field.T_K - 3
    let w0 := -(SymmetricSexticResidual.CoverAlgebra.k5Params.Bv0 *
      SymmetricSexticResidual.CoverAlgebra.k5Params.Av0_inv)
    let z2 := w0 * SymmetricSexticResidual.K5Field.S_K / B
    let q2_0 := (15625 / 59049 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.S_K * A ^ 4
    let d1_1 := (-2384185791015625 / 25942282643925774 : SymmetricSexticResidual.K5Field.K5) *
      (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K +
        77 * SymmetricSexticResidual.K5Field.T_K - 210) *
      SymmetricSexticResidual.K5Field.S_K ^ 6 * (-A) ^ 15 / B ^ 8
    let d0_1 := (-59604644775390625 / 103769130575703096 : SymmetricSexticResidual.K5Field.K5) *
      (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K +
        77 * SymmetricSexticResidual.K5Field.T_K - 189) *
      SymmetricSexticResidual.K5Field.S_K ^ 8 * (-A) ^ 17 / B ^ 12
    let cd := (-59604644775390625 / 4941387170271576 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.S_K ^ 8 * (-A) ^ 17 / B ^ 12
    (d0_1 + z2 * d1_1 = cd ∧
     QuadraticCovers.ValLead 2
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W2_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.res_z)) (cd ^ 2 / q2_0) ∧
     cd ≠ 0 ∧ q2_0 ≠ 0) ∧
    (QuadraticCovers.HasValGe 13
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W1_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.res_z)) ∧
     (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W1_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.res_z)).coeff 13 ≠ 0) := by sorry
