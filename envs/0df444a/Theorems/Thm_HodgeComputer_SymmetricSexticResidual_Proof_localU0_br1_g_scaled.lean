-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_br1_g_scaled
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localU0_br1_g_scaled
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T11:56:16.14721+00:00
-- url     : https://prove2.me/theorems/62d372ba-69fd-4d06-b457-8b56657ef27a
-- title:
--   Scaled valuation bound for $P_{18}$ along Branch 1 ($W_{1,0}$) at $U = 0$
-- statement:
--   Establishes the uniform valuation lower bound on $g(z_1 U + c U)$ for Branch 1 ($W_{1,0}$) above $U = 0$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L1316-L1840

import Definitions.Def_HodgeComputerSSR_BranchHelpers
set_option autoImplicit false
open scoped LaurentSeries

theorem HodgeComputer.SymmetricSexticResidual.Proof.localU0_br1_g_scaled
    {W1s U V ca cb c0W : LaurentSeries SymmetricSexticResidual.K5Field.K5}
    {w2 z1 : SymmetricSexticResidual.K5Field.K5}
    (hw2_ne : w2 ≠ 0)
    (hcb0_ne : (50 / 27 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.S_K *
      (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ≠ 0)
    (hw2_L : QuadraticCovers.ValLead 2 W1s w2)
    (hU_L : QuadraticCovers.ValLead 1 U 1)
    (hV_L : QuadraticCovers.ValLead 1 V w2)
    (hca_L : QuadraticCovers.ValLead 0 ca
      (-(25 / 81 : SymmetricSexticResidual.K5Field.K5) *
        (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) *
        (5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K)))
    (hcb_L : QuadraticCovers.ValLead 0 cb
      ((50 / 27 : SymmetricSexticResidual.K5Field.K5) *
        SymmetricSexticResidual.K5Field.S_K *
        (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)))
    (hc0W_L : QuadraticCovers.ValLead 2 c0W SymmetricSexticResidual.CoverAlgebra.k5Params.c0_V0)
    (hz1_def : z1 = w2 * SymmetricSexticResidual.K5Field.S_K / SymmetricSexticResidual.K5Field.T_K)
    (hw2_eq : SymmetricSexticResidual.K5Field.S_K *
      (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2 * w2 =
      -SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9) ^ 2)
    (hz1_mul : (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2 * z1 =
      -(5 * SymmetricSexticResidual.K5Field.T_K - 9) ^ 2) :
    let g : LaurentSeries SymmetricSexticResidual.K5Field.K5 →
        LaurentSeries SymmetricSexticResidual.K5Field.K5 := fun z =>
      SymmetricSexticResidual.SheetCalculus.P18_of
        (R := LaurentSeries SymmetricSexticResidual.K5Field.K5)
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.y_K)
        (z / W1s) (-(ca * z + c0W) / (W1s * cb)) U V
    ∀ c : SymmetricSexticResidual.K5Field.K5,
      QuadraticCovers.HasValGe 3 (g (HahnSeries.single 2 c)) ∧
      (c = z1 → (g (HahnSeries.single 2 c)).coeff 3 = 0) := by sorry
