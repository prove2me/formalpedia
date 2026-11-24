-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_br1_p4_valDual
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_p4_valDual
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T21:40:23.102225+00:00
-- url     : https://prove2.me/theorems/cb27ba8b-0e1d-483c-9956-6fa9a22f68b4
-- title:
--   Subleading dual-number jet of the leading $z^4$-coefficient $p_4$ on Branch 1 at $U = \infty$
-- statement:
--   Computes the exact `ValDual (-3)` jet $\langle p_{4,-3}, p_{4,-2} \rangle$ of the leading $z^4$-interpolation coefficient $p_4 = (\operatorname{interp4}(g))_1$ on Branch 1 at $U = \infty$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInf.lean#L2499-L2847

import Definitions.Def_HodgeComputerSSR_LocalInfCore
import Definitions.Def_HodgeComputerSSR_LocalInfBiv
set_option autoImplicit false
open scoped LaurentSeries

theorem HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_p4_valDual
    {W1s U V ca cb c0W : LaurentSeries SymmetricSexticResidual.K5Field.K5}
    {w0 w1 : SymmetricSexticResidual.K5Field.K5}
    (hw0_eq : w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.T_K *
      (5 * SymmetricSexticResidual.K5Field.T_K - 9) ^ 2 /
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)
    (hw1_eq : w1 = w0 * ((243 / 4 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.CoverAlgebra.k5Params.Bv1 /
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3))
    (hw0_ne : w0 ≠ 0)
    (hW_D : QuadraticCovers.ValDual 0 W1s ⟨w0, w1⟩)
    (hU_D : QuadraticCovers.ValDual (-1) U (QuadraticCovers.Dual.C 1))
    (hV_D : QuadraticCovers.ValDual 1 V ⟨w0, w1⟩)
    (hca_D : QuadraticCovers.ValDual (-2) ca
      ⟨-(4 / 81 : SymmetricSexticResidual.K5Field.K5) *
        (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 2,
       (143 / 81 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 2 -
        (184 / 27) * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K +
        (52 / 9) * SymmetricSexticResidual.K5Field.Q_K ^ 2⟩)
    (hcb_D : QuadraticCovers.ValDual (-2) cb
      ⟨(4 / 27 : SymmetricSexticResidual.K5Field.K5) *
        (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 2,
       -(92 / 27 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 2 +
        (104 / 9) * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K -
        (22 / 3) * SymmetricSexticResidual.K5Field.Q_K ^ 2 +
        (10 / 7) * SymmetricSexticResidual.K5Field.Q_K + (10 / 7)⟩)
    (hc0W_L : QuadraticCovers.ValLead (-2) c0W
      (-(25 / 81 : SymmetricSexticResidual.K5Field.K5) *
        (5 * SymmetricSexticResidual.K5Field.T_K - 9) *
        (5 * SymmetricSexticResidual.K5Field.T_K - 3))) :
    let g : LaurentSeries SymmetricSexticResidual.K5Field.K5 →
        LaurentSeries SymmetricSexticResidual.K5Field.K5 := fun z =>
      SymmetricSexticResidual.SheetCalculus.P18_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.y_K)
        (z / W1s) (-(ca * z + c0W) / (W1s * cb)) U V
    let S3Q := SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K
    let T59 := 5 * SymmetricSexticResidual.K5Field.T_K - 9
    let p4_m3 : SymmetricSexticResidual.K5Field.K5 :=
      w0⁻¹ ^ 3 * ((73 / 7971615 : SymmetricSexticResidual.K5Field.K5) * T59 * S3Q ^ 2) *
      (SymmetricSexticResidual.LocalResidueU0.evalBivK5
        SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163)
    let p4_m2 : SymmetricSexticResidual.K5Field.K5 :=
      w0⁻¹ ^ 3 * ((73 / 7971615 : SymmetricSexticResidual.K5Field.K5) * T59 * S3Q ^ 2) *
        (SymmetricSexticResidual.LocalResidueU0.evalBivK5
          SymmetricSexticResidual.LocalResidueInf.q1_0_u1_biv / (28 * 107163 * S3Q ^ 3)) +
      w0⁻¹ ^ 3 * (SymmetricSexticResidual.LocalResidueInfAlg.M01_q_fn
          SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
          SymmetricSexticResidual.K5Field.T_K * T59 * S3Q / (267288250950 * S3Q ^ 3)) *
        (SymmetricSexticResidual.LocalResidueU0.evalBivK5
          SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163) +
      w0⁻¹ ^ 2 * ((2 / 885735 : SymmetricSexticResidual.K5Field.K5) * T59 * S3Q ^ 2) *
        (SymmetricSexticResidual.LocalResidueU0.evalBivK5
          SymmetricSexticResidual.LocalResidueInf.cQX_0_biv / 567) *
        (PolynomialEncoding.SignedExpressions.ringEval
          SymmetricSexticResidual.LocalResidueU0.vK5
          SymmetricSexticResidual.VerticalIdentity.H0_int_e / 7) ^ 2
    QuadraticCovers.ValDual (-3) (QuadraticCovers.interp4 g).1 ⟨p4_m3, p4_m2⟩ := by sorry
