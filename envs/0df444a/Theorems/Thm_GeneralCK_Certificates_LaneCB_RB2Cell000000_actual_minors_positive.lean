-- Prove2me | Theorems.Thm_GeneralCK_Certificates_LaneCB_RB2Cell000000_actual_minors_positive
-- name    : GeneralCK.Certificates.LaneCB.RB2Cell000000.actual_minors_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T23:07:29.463288+00:00
-- url     : https://prove2.me/theorems/ea15c8c6-0ce9-45bb-97f1-4531ca283f16
-- title:
--   Correction matrix positivity on the first RB2 cell
-- statement:
--   For $1/10\le u\le257/2560$ and $1/10\le\rho\le53/512$, with $\rho<1$, put $w=u+\rho(1/2-u)$. The correction matrix at entropy coordinates $(H(u),H(w))$ has strictly positive first diagonal entry $M_{\rm left}$ and determinant $M_{\rm det}$.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_correction_minors
import Definitions.Def_GeneralCK_statement

open Set
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem GeneralCK.Certificates.LaneCB.RB2Cell000000.actual_minors_positive {u rho : ℝ} (hu : u∈Icc (1/10:ℝ) (257/2560))
    (hr : rho∈Icc (1/10:ℝ) (53/512)) (hr1 : rho < 1) :
    0 < _root_.GeneralCK.Correction.Mleft (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) ∧
    0 < _root_.GeneralCK.Correction.Mdet (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) := by sorry
