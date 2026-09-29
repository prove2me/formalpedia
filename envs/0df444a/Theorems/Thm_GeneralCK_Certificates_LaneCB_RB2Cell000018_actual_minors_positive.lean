-- Prove2me | Theorems.Thm_GeneralCK_Certificates_LaneCB_RB2Cell000018_actual_minors_positive
-- name    : GeneralCK.Certificates.LaneCB.RB2Cell000018.actual_minors_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T01:30:26.049854+00:00
-- url     : https://prove2.me/theorems/a4b5b8ef-08ac-4722-8120-620d1b646129
-- title:
--   Correction matrix positivity on RB2 cell 000018
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

theorem GeneralCK.Certificates.LaneCB.RB2Cell000018.actual_minors_positive {u rho : ℝ} (hu : u∈Icc (257/2560:ℝ) (129/1280))
    (hr : rho∈Icc (73/640:ℝ) (301/2560)) (hr1 : rho < 1) :
    0 < _root_.GeneralCK.Correction.Mleft (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) ∧
    0 < _root_.GeneralCK.Correction.Mdet (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) := by sorry
