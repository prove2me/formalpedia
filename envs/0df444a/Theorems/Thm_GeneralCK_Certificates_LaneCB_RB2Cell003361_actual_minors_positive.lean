-- Prove2me | Theorems.Thm_GeneralCK_Certificates_LaneCB_RB2Cell003361_actual_minors_positive
-- name    : GeneralCK.Certificates.LaneCB.RB2Cell003361.actual_minors_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T23:33:11.177173+00:00
-- url     : https://prove2.me/theorems/b55d4a09-b5dc-4c9e-beeb-a8bdba8d212e
-- title:
--   Correction matrix positivity on RB2 cell 003361
-- statement:
--   For $75/512\le u\le47/320$ and $109/640\le\rho\le227/1280$, with $\rho<1$, put $w=u+\rho(1/2-u)$. The correction matrix at entropy coordinates $(H(u),H(w))$ has strictly positive first diagonal entry $M_{\rm left}$ and determinant $M_{\rm det}$.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_correction_minors
import Definitions.Def_GeneralCK_statement

open Set
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem GeneralCK.Certificates.LaneCB.RB2Cell003361.actual_minors_positive {u rho : ℝ} (hu : u∈Icc (75/512:ℝ) (47/320))
    (hr : rho∈Icc (109/640:ℝ) (227/1280)) (hr1 : rho < 1) :
    0 < _root_.GeneralCK.Correction.Mleft (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) ∧
    0 < _root_.GeneralCK.Correction.Mdet (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) := by sorry
