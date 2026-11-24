-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_br1_g_valLead
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_g_valLead
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-24T20:35:55.995432+00:00
-- url     : https://prove2.me/theorems/754d0481-2d58-457a-adcd-1bc6ceb6282f
-- title:
--   Leading $O(t^{-3})$ Laurent jet of $P_{18}(z)$ on Branch 1 at $U = \infty$
-- statement:
--   Computes `ValLead (-3)` of $P_{18}$ along Branch 1 ($W_{1,\infty}$) at $U = \infty$ for every constant $z \in K_5$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInf.lean#L1746-L2053

import Definitions.Def_HodgeComputerSSR_LocalInfCore
import Definitions.Def_HodgeComputerSSR_LocalInfBiv
set_option autoImplicit false
open scoped LaurentSeries

theorem HodgeComputer.SymmetricSexticResidual.Proof.localInf_br1_g_valLead
    {W1s U V ca cb c0W : LaurentSeries SymmetricSexticResidual.K5Field.K5}
    {w0 : SymmetricSexticResidual.K5Field.K5}
    (hw0_eq : w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9) ^ 2 /
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hW_L : QuadraticCovers.ValLead 0 W1s w0)
    (hU_L : QuadraticCovers.ValLead (-1) U 1)
    (hV_L : QuadraticCovers.ValLead 1 V w0)
    (hca_L : QuadraticCovers.ValLead (-2) ca (-(4 / 81 : SymmetricSexticResidual.K5Field.K5) *
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 2))
    (hcb_L : QuadraticCovers.ValLead (-2) cb ((4 / 27 : SymmetricSexticResidual.K5Field.K5) *
      (SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) ^ 2))
    (hc0W_L : QuadraticCovers.ValLead (-2) c0W (-(25 / 81 : SymmetricSexticResidual.K5Field.K5) *
      (5 * SymmetricSexticResidual.K5Field.T_K - 9) * (5 * SymmetricSexticResidual.K5Field.T_K - 3))) :
    ∀ z : SymmetricSexticResidual.K5Field.K5, QuadraticCovers.ValLead (-3)
      (SymmetricSexticResidual.SheetCalculus.P18_of
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.y_K)
        (HahnSeries.C z / W1s) (-(ca * HahnSeries.C z + c0W) / (W1s * cb)) U V)
      ((w0 * SymmetricSexticResidual.LocalResidueInfAlg.A0V_Uk 3 (z / w0)
        (z / w0 / 3 + -(SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
          (5 * SymmetricSexticResidual.K5Field.T_K - 3) /
          (3 * SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9)))
        (SymmetricSexticResidual.K5Field.S_K - z / w0 * SymmetricSexticResidual.K5Field.T_K)
        (SymmetricSexticResidual.K5Field.Q_K - (z / w0 / 3 +
          -(SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
          (5 * SymmetricSexticResidual.K5Field.T_K - 3) /
          (3 * SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9))) *
          SymmetricSexticResidual.K5Field.T_K)) *
       ((SymmetricSexticResidual.LocalResidueU0.evalBivK5
          SymmetricSexticResidual.LocalResidueInf.q1_m1_u1_biv / 107163) * (z / w0) +
        (SymmetricSexticResidual.LocalResidueU0.evalBivK5
          SymmetricSexticResidual.LocalResidueInf.q1_m1_u0_biv /
          (3 * SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9) * 107163)))) := by sorry
