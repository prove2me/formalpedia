-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_valAC_P18
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.cover_valAC_P18
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T09:36:18.438216+00:00
-- url     : https://prove2.me/theorems/3d3131c9-dd4c-4c54-8b77-74675c3860db
-- title:
--   Pointwise evaluation of $P_{18}$ and dual-number Jacobian identity on $R_{34}$
-- statement:
--   Evaluates the 5-point interpolated numerator $P_{18,z}$ and the first-order dual-number cover derivative at each active branch $(r, w_1)$ above $r \in R_{34}$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverResidue.lean#L2701-L3640

import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.cover_valAC_P18 :
    (∀ {r w : SymmetricSexticResidual.CoverResidue.CoverL},
      r ≠ 0 → r ≠ 1 → w ≠ 0 →
      (SymmetricSexticResidual.CoverAlgebra.k5Params.cb_h.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r ≠ 0 →
      (SymmetricSexticResidual.CoverAlgebra.k5Params.nm_WU.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r ≠ 0 →
      w ^ 2 + (SymmetricSexticResidual.CoverAlgebra.k5Params.bW.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r * w +
        (SymmetricSexticResidual.CoverAlgebra.k5Params.cW.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r = 0 →
      ∀ {z : SymmetricSexticResidual.CoverResidue.A_C} {vz : SymmetricSexticResidual.CoverResidue.CoverL},
      SymmetricSexticResidual.CoverResidue.ValAC r w z vz →
      SymmetricSexticResidual.CoverResidue.ValAC r w (SymmetricSexticResidual.CoverResidue.P18_z_AC z)
        (SymmetricSexticResidual.SheetCalculus.P18_of
          (SymmetricSexticResidual.SheetCalculus.SL (L := SymmetricSexticResidual.CoverResidue.CoverL))
          SymmetricSexticResidual.SheetCalculus.QL SymmetricSexticResidual.SheetCalculus.TL
          SymmetricSexticResidual.SheetCalculus.xL SymmetricSexticResidual.SheetCalculus.yL
          (vz / w)
          (-(SymmetricSexticResidual.CoverResidue.pU SymmetricSexticResidual.CoverResidue.ιL_K5
              SymmetricSexticResidual.CoverAlgebra.k5Params.ca_h r * vz +
            SymmetricSexticResidual.CoverResidue.pUW SymmetricSexticResidual.CoverResidue.ιL_K5
              SymmetricSexticResidual.CoverAlgebra.k5Params.c0W r w) /
            (w * SymmetricSexticResidual.CoverResidue.pU SymmetricSexticResidual.CoverResidue.ιL_K5
              SymmetricSexticResidual.CoverAlgebra.k5Params.cb_h r))
          r (w / r))) ∧
    (∀ {r w : SymmetricSexticResidual.CoverResidue.CoverL},
      w ^ 2 + (SymmetricSexticResidual.CoverAlgebra.k5Params.bW.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r * w +
        (SymmetricSexticResidual.CoverAlgebra.k5Params.cW.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r = 0 →
      ∀ {f : SymmetricSexticResidual.CoverResidue.A_C → SymmetricSexticResidual.CoverResidue.A_C}
        {g : SymmetricSexticResidual.CoverResidue.CoverL → SymmetricSexticResidual.CoverResidue.CoverL},
      (∀ {z : SymmetricSexticResidual.CoverResidue.A_C} {vz : SymmetricSexticResidual.CoverResidue.CoverL},
        SymmetricSexticResidual.CoverResidue.ValAC r w z vz →
        SymmetricSexticResidual.CoverResidue.ValAC r w (f z) (g vz)) →
      let p := QuadraticCovers.interp4 f; let q := QuadraticCovers.interp4 g
      SymmetricSexticResidual.CoverResidue.ValAC r w p.1 q.1 ∧
      SymmetricSexticResidual.CoverResidue.ValAC r w p.2.1 q.2.1 ∧
      SymmetricSexticResidual.CoverResidue.ValAC r w p.2.2.1 q.2.2.1 ∧
      SymmetricSexticResidual.CoverResidue.ValAC r w p.2.2.2.1 q.2.2.2.1 ∧
      SymmetricSexticResidual.CoverResidue.ValAC r w p.2.2.2.2 q.2.2.2.2) ∧
    (∀ {r w : SymmetricSexticResidual.CoverResidue.CoverL},
      w ^ 2 + (SymmetricSexticResidual.CoverAlgebra.k5Params.bW.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r * w +
        (SymmetricSexticResidual.CoverAlgebra.k5Params.cW.map SymmetricSexticResidual.CoverResidue.ιL_K5).eval r = 0 →
      ∀ {q2 q1 q0 p4 p3 p2 p1 p0 : SymmetricSexticResidual.CoverResidue.A_C}
        {vq2 vq1 vq0 vp4 vp3 vp2 vp1 vp0 : SymmetricSexticResidual.CoverResidue.CoverL},
      SymmetricSexticResidual.CoverResidue.ValAC r w q2 vq2 →
      SymmetricSexticResidual.CoverResidue.ValAC r w q1 vq1 →
      SymmetricSexticResidual.CoverResidue.ValAC r w q0 vq0 →
      SymmetricSexticResidual.CoverResidue.ValAC r w p4 vp4 →
      SymmetricSexticResidual.CoverResidue.ValAC r w p3 vp3 →
      SymmetricSexticResidual.CoverResidue.ValAC r w p2 vp2 →
      SymmetricSexticResidual.CoverResidue.ValAC r w p1 vp1 →
      SymmetricSexticResidual.CoverResidue.ValAC r w p0 vp0 →
      SymmetricSexticResidual.CoverResidue.ValAC r w
        (QuadraticCovers.remDeg4_P1 q2 q1 q0 p4 p3 p2 p1)
        (QuadraticCovers.remDeg4_P1 vq2 vq1 vq0 vp4 vp3 vp2 vp1) ∧
      SymmetricSexticResidual.CoverResidue.ValAC r w
        (QuadraticCovers.remDeg4_P0 q2 q1 q0 p4 p3 p2 p0)
        (QuadraticCovers.remDeg4_P0 vq2 vq1 vq0 vp4 vp3 vp2 vp0)) := by sorry
