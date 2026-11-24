-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_br2_g_lead
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_g_lead
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T12:53:28.688972+00:00
-- url     : https://prove2.me/theorems/b6d2ab25-18af-41e3-9a61-9615fc6f409c
-- title:
--   Leading Laurent expansion of $P_{18}$ along Branch 2 ($W_{2,0}$) at $U = 0$
-- statement:
--   Computes the exact leading valuation and coefficient of $P_{18}$ on Branch 2 ($W_{2,0}$) above $U = 0$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L2666-L3310

import Definitions.Def_HodgeComputerSSR_BranchHelpers
set_option autoImplicit false
open scoped LaurentSeries

theorem HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_g_lead :
    (∀ (mi : Fin 10) (a b : SymmetricSexticResidual.K5Field.K5),
      SymmetricSexticResidual.LocalResidueU0.numM_12_of (RingHom.id SymmetricSexticResidual.K5Field.K5) mi a b =
        (8 * (SymmetricSexticResidual.SheetCalculus.numM mi a b
                (SymmetricSexticResidual.K5Field.S_K - a * SymmetricSexticResidual.K5Field.T_K)
                (SymmetricSexticResidual.K5Field.Q_K - b * SymmetricSexticResidual.K5Field.T_K) 1 1 -
              SymmetricSexticResidual.SheetCalculus.numM mi a b
                (SymmetricSexticResidual.K5Field.S_K - a * SymmetricSexticResidual.K5Field.T_K)
                (SymmetricSexticResidual.K5Field.Q_K - b * SymmetricSexticResidual.K5Field.T_K) (-1) 1) -
          (SymmetricSexticResidual.SheetCalculus.numM mi a b
                (SymmetricSexticResidual.K5Field.S_K - a * SymmetricSexticResidual.K5Field.T_K)
                (SymmetricSexticResidual.K5Field.Q_K - b * SymmetricSexticResidual.K5Field.T_K) 2 1 -
           SymmetricSexticResidual.SheetCalculus.numM mi a b
                (SymmetricSexticResidual.K5Field.S_K - a * SymmetricSexticResidual.K5Field.T_K)
                (SymmetricSexticResidual.K5Field.Q_K - b * SymmetricSexticResidual.K5Field.T_K) (-2) 1)) / 12) ∧
    (∀ {W2s U V ca cb c0W : LaurentSeries SymmetricSexticResidual.K5Field.K5}
      {w0 ca0 cb0 c0W0 : SymmetricSexticResidual.K5Field.K5},
      w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K *
        (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2 /
        (SymmetricSexticResidual.K5Field.T_K - 3) ^ 3 →
      w0 ≠ 0 → cb0 ≠ 0 →
      ca0 = -(25 / 81 : SymmetricSexticResidual.K5Field.K5) *
        (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) *
        (5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) →
      cb0 = (50 / 27 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K *
        (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) →
      c0W0 = SymmetricSexticResidual.CoverAlgebra.k5Params.c0_V2 * w0 ^ 2 →
      QuadraticCovers.ValLead 0 W2s w0 →
      QuadraticCovers.ValLead 1 U 1 →
      QuadraticCovers.ValLead (-1) V w0 →
      QuadraticCovers.ValLead 0 ca ca0 →
      QuadraticCovers.ValLead 0 cb cb0 →
      QuadraticCovers.ValLead 0 c0W c0W0 →
      let q1_lead0 : SymmetricSexticResidual.K5Field.K5 →
          SymmetricSexticResidual.K5Field.K5 → SymmetricSexticResidual.K5Field.K5 := fun a b =>
        let qY0 := 9 * ((SymmetricSexticResidual.SheetCalculus.QY_num
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 1 0 -
          SymmetricSexticResidual.SheetCalculus.QY_num
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 0 0) * a +
          (SymmetricSexticResidual.SheetCalculus.QY_num
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 1 1 -
          SymmetricSexticResidual.SheetCalculus.QY_num
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 0 1) * b +
          (SymmetricSexticResidual.SheetCalculus.QY_num
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 1 2 -
          SymmetricSexticResidual.SheetCalculus.QY_num
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 0 2))
        let cA0 := 9 * ((SymmetricSexticResidual.SheetCalculus.H0_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K *
          SymmetricSexticResidual.SheetCalculus.dA1_fn 0
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 -
          SymmetricSexticResidual.SheetCalculus.A1_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 *
          SymmetricSexticResidual.SheetCalculus.dH0_fn 0
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K) * a +
          (SymmetricSexticResidual.SheetCalculus.H0_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K *
          SymmetricSexticResidual.SheetCalculus.dA1_fn 1
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 -
          SymmetricSexticResidual.SheetCalculus.A1_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 *
          SymmetricSexticResidual.SheetCalculus.dH0_fn 1
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K) * b +
          (SymmetricSexticResidual.SheetCalculus.H0_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K *
          SymmetricSexticResidual.SheetCalculus.dA1_fn 2
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 -
          SymmetricSexticResidual.SheetCalculus.A1_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 *
          SymmetricSexticResidual.SheetCalculus.dH0_fn 2
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K))
        w0 * (SymmetricSexticResidual.SheetCalculus.H0_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K *
          SymmetricSexticResidual.SheetCalculus.A1_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 * qY0 +
          cA0 * SymmetricSexticResidual.SheetCalculus.EB_of
            SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
            SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K
            SymmetricSexticResidual.K5Field.y_K 0 1)
      ∀ z : SymmetricSexticResidual.K5Field.K5,
        let a := z / w0; let b := -(ca0 * z + c0W0) / (w0 * cb0)
        QuadraticCovers.ValLead (-3)
          (SymmetricSexticResidual.SheetCalculus.P18_of
            (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
            (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
            (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
            (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
            (HahnSeries.C SymmetricSexticResidual.K5Field.y_K)
            (HahnSeries.C z / W2s) (-(ca * HahnSeries.C z + c0W) / (W2s * cb)) U V)
          (w0 ^ 2 * SymmetricSexticResidual.LocalResidueU0.A0U_12_of
            (RingHom.id SymmetricSexticResidual.K5Field.K5) a b * q1_lead0 a b)) := by sorry
