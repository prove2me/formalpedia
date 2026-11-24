-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_br1_fV
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_fV
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T20:06:12.536737+00:00
-- url     : https://prove2.me/theorems/0762bffb-f204-4930-b368-5aa14b0535b0
-- title:
--   Subleading dual-number jet of the 3rd finite difference of $A_{0V}/V$ on Branch 1 at $U = \infty$
-- statement:
--   Computes the exact `ValDual (-2)` jet of the 3rd finite difference of $f_V(z) = A_{0V} / V$ along Branch 1 ($W_{1,\infty}$) at $U = \infty$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInf.lean#L2125-L2302

import Definitions.Def_HodgeComputerSSR_LocalInfCore
set_option autoImplicit false
open scoped LaurentSeries

theorem HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_fV
    {U V aa rca ab b0s : LaurentSeries SymmetricSexticResidual.K5Field.K5}
    {w0 w1 : SymmetricSexticResidual.K5Field.K5}
    (hw1_eq : w1 = w0 * ((243 / 4 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.CoverAlgebra.k5Params.Bv1 /
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3))
    (hw0_ne : w0 ≠ 0) (hab_eq : ab = rca * aa)
    (hU_D : QuadraticCovers.ValDual (-1) U (QuadraticCovers.Dual.C 1))
    (hV_D : QuadraticCovers.ValDual 1 V ⟨w0, w1⟩)
    (hrca_D : QuadraticCovers.ValDual 0 rca ⟨1 / 3, (-(3 / 28 : SymmetricSexticResidual.K5Field.K5) *
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
      (119 * SymmetricSexticResidual.K5Field.S_K ^ 2 -
       560 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K +
       630 * SymmetricSexticResidual.K5Field.Q_K ^ 2 + 90 * SymmetricSexticResidual.K5Field.Q_K + 90)) /
      (3 * (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)⟩)
    (haa_D : QuadraticCovers.ValDual 0 aa ⟨w0⁻¹, -w1 / w0 ^ 2⟩)
    (hab_D : QuadraticCovers.ValDual 0 ab (⟨1 / 3, (-(3 / 28 : SymmetricSexticResidual.K5Field.K5) *
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
      (119 * SymmetricSexticResidual.K5Field.S_K ^ 2 -
       560 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K +
       630 * SymmetricSexticResidual.K5Field.Q_K ^ 2 + 90 * SymmetricSexticResidual.K5Field.Q_K + 90)) /
      (3 * (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)⟩ * ⟨w0⁻¹, -w1 / w0 ^ 2⟩))
    (hb0_L : QuadraticCovers.ValLead 0 b0s
      (-((SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
        (5 * SymmetricSexticResidual.K5Field.T_K - 3)) /
        (3 * SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9)))) :
    let fV : LaurentSeries SymmetricSexticResidual.K5Field.K5 → LaurentSeries SymmetricSexticResidual.K5Field.K5 := fun z =>
      SymmetricSexticResidual.SheetCalculus.A_0V (aa * z) (ab * z + b0s)
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K - aa * z * HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K - (ab * z + b0s) * HahnSeries.C SymmetricSexticResidual.K5Field.T_K) U V / V
    let S3Q := SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K
    let T59 := 5 * SymmetricSexticResidual.K5Field.T_K - 9
    QuadraticCovers.ValDual (-2) ((fV 2 - 3 * fV 1 + 3 * fV 0 - fV (-1)) / 6)
      ⟨w0⁻¹ ^ 2 * ((73 / 7971615 : SymmetricSexticResidual.K5Field.K5) * T59 * S3Q ^ 2),
       w0⁻¹ ^ 2 * (SymmetricSexticResidual.LocalResidueInfAlg.M01_q_fn
         SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K
         SymmetricSexticResidual.K5Field.T_K * T59 * S3Q / (267288250950 * S3Q ^ 3))⟩ := by sorry
