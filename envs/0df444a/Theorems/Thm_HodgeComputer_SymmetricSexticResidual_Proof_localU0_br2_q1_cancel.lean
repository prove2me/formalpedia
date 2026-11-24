-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_br2_q1_cancel
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_q1_cancel
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-24T14:20:52.567018+00:00
-- url     : https://prove2.me/theorems/d2ac0465-e8d9-4237-9bab-d7178bf1f3ae
-- title:
--   Bivariate evaluation of $q_1$ and final $K_5$ cancellation for Branch 2 at $U = 0$
-- statement:
--   Combines the bivariate AST evaluations of `q1_v_35721_biv` and `q1_e_35721_divB5_biv` with `localU0_biv_identity` to cancel the cleared Branch-2 residue ratio to `toK5_RU`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L3765-L4060

import Definitions.Def_HodgeComputerSSR_CoverParams
import Definitions.Def_HodgeComputerSSR_RUData
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_q1_cancel
    {w0 P_val P_eps P1_0 P0_0 : SymmetricSexticResidual.K5Field.K5}
    (hw0_eq : w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hden_ne : 81 * SymmetricSexticResidual.CoverAlgebra.k5Params.Av0 * w0 *
      ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4) ^ 3 *
      (((-59604644775390625 / 4941387170271576 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12) ^ 2 /
        ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4)) ≠ 0)
    (hq2_ne : (15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4 ≠ 0)
    (hcd_eq : ((-59604644775390625 / 103769130575703096 : SymmetricSexticResidual.K5Field.K5) *
        (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K + 77 * SymmetricSexticResidual.K5Field.T_K - 189) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12) +
      (w0 * SymmetricSexticResidual.K5Field.S_K / (SymmetricSexticResidual.K5Field.T_K - 3)) *
        ((-2384185791015625 / 25942282643925774 : SymmetricSexticResidual.K5Field.K5) *
          (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K + 77 * SymmetricSexticResidual.K5Field.T_K - 210) * SymmetricSexticResidual.K5Field.S_K ^ 6 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 15 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 8) =
      (-59604644775390625 / 4941387170271576 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12)
    (hP_val : ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4) ^ 3 * P_val =
      P1_0 * (w0 * SymmetricSexticResidual.K5Field.S_K / (SymmetricSexticResidual.K5Field.T_K - 3)) + P0_0)
    (hP_eps : ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4) ^ 3 * P_eps = P1_0 * w0)
    (hPg0_Z2_prod :
      let q1_c := fun k : Fin 3 =>
        9 * w0 * (SymmetricSexticResidual.SheetCalculus.H0_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K * SymmetricSexticResidual.SheetCalculus.A1_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 *
            (SymmetricSexticResidual.SheetCalculus.QY_num SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K SymmetricSexticResidual.K5Field.y_K 0 1 k - SymmetricSexticResidual.SheetCalculus.QY_num SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K SymmetricSexticResidual.K5Field.y_K 0 0 k) +
          (SymmetricSexticResidual.SheetCalculus.H0_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K * SymmetricSexticResidual.SheetCalculus.dA1_fn k SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 -
            SymmetricSexticResidual.SheetCalculus.A1_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 * SymmetricSexticResidual.SheetCalculus.dH0_fn k SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K) *
            SymmetricSexticResidual.SheetCalculus.EB_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K SymmetricSexticResidual.K5Field.y_K 0 1)
      QuadraticCovers.Dual.C (35721 * (6 * SymmetricSexticResidual.K5Field.S_K * (SymmetricSexticResidual.K5Field.T_K - 3)) ^ 4) * ⟨P_val, P_eps⟩ =
      QuadraticCovers.Dual.C (w0 ^ 2) *
        ⟨(8248380 / 51331077 : SymmetricSexticResidual.K5Field.K5) * (5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) * SymmetricSexticResidual.K5Field.S_K ^ 3 * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2,
         -(2 / 51331077 : SymmetricSexticResidual.K5Field.K5) * (SymmetricSexticResidual.K5Field.T_K - 3) * SymmetricSexticResidual.K5Field.S_K ^ 2 * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2 *
           (11943020 * SymmetricSexticResidual.K5Field.S_K ^ 2 - 876486 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K + 8382500 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.T_K +
            5029500 * SymmetricSexticResidual.K5Field.Q_K * SymmetricSexticResidual.K5Field.T_K - 14837025 * SymmetricSexticResidual.K5Field.S_K - 33647355 * SymmetricSexticResidual.K5Field.Q_K)⟩ *
        ⟨35721 * (q1_c 0 * (6 * SymmetricSexticResidual.K5Field.S_K ^ 2) + q1_c 1 * (6 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K) + q1_c 2 * (6 * SymmetricSexticResidual.K5Field.S_K * (SymmetricSexticResidual.K5Field.T_K - 3))),
         35721 * (q1_c 0 * (6 * SymmetricSexticResidual.K5Field.S_K * (SymmetricSexticResidual.K5Field.T_K - 3)) + q1_c 1 * ((5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) * (SymmetricSexticResidual.K5Field.T_K - 3)))⟩) :
    -(P1_0 * ((-59604644775390625 / 103769130575703096 : SymmetricSexticResidual.K5Field.K5) *
        (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K + 77 * SymmetricSexticResidual.K5Field.T_K - 189) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12) -
      P0_0 * ((-2384185791015625 / 25942282643925774 : SymmetricSexticResidual.K5Field.K5) *
        (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K + 77 * SymmetricSexticResidual.K5Field.T_K - 210) * SymmetricSexticResidual.K5Field.S_K ^ 6 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 15 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 8)) *
      w0 * ((50 / 27 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 4 /
      (81 * SymmetricSexticResidual.CoverAlgebra.k5Params.Av0 * w0 *
        ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4) ^ 3 *
        (((-59604644775390625 / 4941387170271576 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12) ^ 2 /
          ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4))) =
    SymmetricSexticResidual.LocalResidueU0.toK5_RU := by sorry
