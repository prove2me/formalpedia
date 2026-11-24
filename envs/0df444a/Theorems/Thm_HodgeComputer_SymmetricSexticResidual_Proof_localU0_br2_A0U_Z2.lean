-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_br2_A0U_Z2
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_A0U_Z2
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T13:53:07.48606+00:00
-- url     : https://prove2.me/theorems/bb19444a-1e42-49f6-9985-8f4e96230e9a
-- title:
--   First-order dual expansion of $A_{0U}$ at the double root $z_2$ on Branch 2 at $U = 0$
-- statement:
--   Computes the exact first-order `Dual K5` jet of $A_{0U}$ along Branch 2 at the leading double root $z_2 = w_0 S / (T - 3)$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L3531-L3765

import Definitions.Def_HodgeComputerSSR_BranchHelpers
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_A0U_Z2 :
    let A := 5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K
    let B := SymmetricSexticResidual.K5Field.T_K - 3
    let d_ab := 6 * SymmetricSexticResidual.K5Field.S_K * B
    let Q_quad := 11943020 * SymmetricSexticResidual.K5Field.S_K ^ 2 -
      876486 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K +
      8382500 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.T_K +
      5029500 * SymmetricSexticResidual.K5Field.Q_K * SymmetricSexticResidual.K5Field.T_K -
      14837025 * SymmetricSexticResidual.K5Field.S_K - 33647355 * SymmetricSexticResidual.K5Field.Q_K
    let a_du : QuadraticCovers.Dual SymmetricSexticResidual.K5Field.K5 :=
      QuadraticCovers.Dual.C d_ab⁻¹ * ⟨6 * SymmetricSexticResidual.K5Field.S_K ^ 2, 6 * SymmetricSexticResidual.K5Field.S_K * B⟩
    let b_du : QuadraticCovers.Dual SymmetricSexticResidual.K5Field.K5 :=
      QuadraticCovers.Dual.C d_ab⁻¹ * ⟨6 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K,
        (5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) * B⟩
    QuadraticCovers.Dual.C (d_ab ^ 3) *
      SymmetricSexticResidual.LocalResidueU0.A0U_12_of QuadraticCovers.Dual.C a_du b_du =
      ⟨(8248380 / 51331077 : SymmetricSexticResidual.K5Field.K5) *
        (5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
        SymmetricSexticResidual.K5Field.S_K ^ 3 * A ^ 2,
       -(2 / 51331077 : SymmetricSexticResidual.K5Field.K5) * B *
        SymmetricSexticResidual.K5Field.S_K ^ 2 * A ^ 2 * Q_quad⟩ := by sorry
