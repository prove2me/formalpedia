-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_br1_q1_valDual
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_q1_valDual
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T21:03:18.727801+00:00
-- url     : https://prove2.me/theorems/c0c343a4-087b-44cc-b5fd-12833ba06815
-- title:
--   First-order dual jets of the linear differences of $q_Y$, $q_X$, and $q_1$ on Branch 1 at $U = \infty$
-- statement:
--   Computes the exact `ValDual` jets of $h_{qY}(1) - h_{qY}(0)$, $h_{qX}(1) - h_{qX}(0)$, and $h_{q1}(1) - h_{q1}(0)$ along Branch 1 ($W_{1,\infty}$) at $U = \infty$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInf.lean#L2053-L2499

import Definitions.Def_HodgeComputerSSR_LocalInfCore
import Definitions.Def_HodgeComputerSSR_LocalInfBiv
set_option autoImplicit false
open scoped LaurentSeries

theorem HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_q1_valDual
    {U V aa ab b0s : LaurentSeries SymmetricSexticResidual.K5Field.K5}
    {w0 w1 : SymmetricSexticResidual.K5Field.K5}
    (hw0_eq : w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9) ^ 2 /
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)
    (hw1_eq : w1 = w0 * ((243 / 4 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.CoverAlgebra.k5Params.Bv1 /
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3))
    (hw0_ne : w0 ≠ 0)
    (hU_D : QuadraticCovers.ValDual (-1) U (QuadraticCovers.Dual.C 1))
    (hV_D : QuadraticCovers.ValDual 1 V ⟨w0, w1⟩)
    (haa_D : QuadraticCovers.ValDual 0 aa ⟨w0⁻¹, -w1 / w0 ^ 2⟩)
    (hab_D : QuadraticCovers.ValDual 0 ab (⟨1 / 3, (-(3 / 28 : SymmetricSexticResidual.K5Field.K5) *
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
      (119 * SymmetricSexticResidual.K5Field.S_K ^ 2 -
       560 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K +
       630 * SymmetricSexticResidual.K5Field.Q_K ^ 2 + 90 * SymmetricSexticResidual.K5Field.Q_K + 90)) /
      (3 * (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩)) :
    let hqY : LaurentSeries SymmetricSexticResidual.K5Field.K5 → LaurentSeries SymmetricSexticResidual.K5Field.K5 := fun z =>
      SymmetricSexticResidual.SheetCalculus.dot_ab
        (SymmetricSexticResidual.SheetCalculus.QY_num
          (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.y_K) U V) (aa * z) (ab * z + b0s) /
        SymmetricSexticResidual.SheetCalculus.v_of V
    let hqX : LaurentSeries SymmetricSexticResidual.K5Field.K5 → LaurentSeries SymmetricSexticResidual.K5Field.K5 := fun z =>
      SymmetricSexticResidual.SheetCalculus.dot_ab
        (SymmetricSexticResidual.SheetCalculus.QX_num
          (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.y_K) U V) (aa * z) (ab * z + b0s) /
        SymmetricSexticResidual.SheetCalculus.u_of U
    let hq1 : LaurentSeries SymmetricSexticResidual.K5Field.K5 → LaurentSeries SymmetricSexticResidual.K5Field.K5 := fun z =>
      SymmetricSexticResidual.SheetCalculus.H0_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K) *
      SymmetricSexticResidual.SheetCalculus.A1_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K) U V * hqY z +
      SymmetricSexticResidual.SheetCalculus.H0_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K) *
      SymmetricSexticResidual.SheetCalculus.B1_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K) U V * hqX z +
      (SymmetricSexticResidual.SheetCalculus.cA1_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K) (aa * z) (ab * z + b0s) U V /
        SymmetricSexticResidual.SheetCalculus.v_of V) *
        SymmetricSexticResidual.SheetCalculus.EB_of
          (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
          (HahnSeries.C SymmetricSexticResidual.K5Field.y_K) U V
    let S3Q := SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K
    let r1 : SymmetricSexticResidual.K5Field.K5 :=
      (-(3 / 28 : SymmetricSexticResidual.K5Field.K5) * S3Q *
        (119 * SymmetricSexticResidual.K5Field.S_K ^ 2 -
         560 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K +
         630 * SymmetricSexticResidual.K5Field.Q_K ^ 2 + 90 * SymmetricSexticResidual.K5Field.Q_K + 90)) / (3 * S3Q ^ 3)
    QuadraticCovers.ValDual (-1) (hqY 1 - hqY 0)
      ⟨0, -9 * w0⁻¹ * (r1 * SymmetricSexticResidual.LocalResidueU0.evalBivK5
          (SymmetricSexticResidual.LocalResidueInf.QY10_biv 1) / 1701 +
        SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.cQY_00_biv / 5103 +
        w0 * SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.cQY_11_biv / 5103)⟩ ∧
    QuadraticCovers.ValDual 0 (hqX 1 - hqX 0)
      ⟨w0⁻¹ * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.cQX_0_biv / 567),
       w0⁻¹ * ((SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.cQX_1_biv +
         28 * S3Q ^ 3 * SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.cQX_0_biv) /
         (28 * 567 * S3Q ^ 3))⟩ ∧
    QuadraticCovers.ValDual (-1) (hq1 1 - hq1 0)
      ⟨w0⁻¹ * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163),
       w0⁻¹ * (SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.q1_0_u1_biv /
         (28 * 107163 * S3Q ^ 3))⟩ := by sorry
