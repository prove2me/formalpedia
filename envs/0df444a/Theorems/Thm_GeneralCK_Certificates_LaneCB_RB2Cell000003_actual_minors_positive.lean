-- Prove2me | Theorems.Thm_GeneralCK_Certificates_LaneCB_RB2Cell000003_actual_minors_positive
-- name    : GeneralCK.Certificates.LaneCB.RB2Cell000003.actual_minors_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:02:51.880432+00:00
-- url     : https://prove2.me/theorems/bbbc8167-af63-40df-b482-6ff50ec0b80f
-- title:
--   Correction matrix positivity on RB2 cell 000003
-- statement:
--   For real $u,\rho$ in the cell's specified closed intervals, with $\rho<1$, put $w=u+\rho(1/2-u)$. The correction matrix at entropy coordinates $(H(u),H(w))$ has strictly positive first diagonal entry $M_{\rm left}$ and determinant $M_{\rm det}$. The exact interval endpoints appear in the formal statement.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_correction_minors
import Definitions.Def_GeneralCK_statement

open Set
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem GeneralCK.Certificates.LaneCB.RB2Cell000003.actual_minors_positive {u rho : ℝ} (hu : u∈Icc (257/2560:ℝ) (129/1280))
    (hr : rho∈Icc (53/512:ℝ) (137/1280)) (hr1 : rho < 1) :
    0 < _root_.GeneralCK.Correction.Mleft (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) ∧
    0 < _root_.GeneralCK.Correction.Mdet (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) := by sorry
