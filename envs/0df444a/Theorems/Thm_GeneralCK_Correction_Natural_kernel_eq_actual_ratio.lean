-- Prove2me | Theorems.Thm_GeneralCK_Correction_Natural_kernel_eq_actual_ratio
-- name    : GeneralCK.Correction.Natural.kernel_eq_actual_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:52:53.911349+00:00
-- url     : https://prove2.me/theorems/e8d0e20d-f959-4a42-a3ba-79fa09bff3ad
-- title:
--   Natural correction kernels at an interior ratio point
-- statement:
--   If $0<u<1/2$ and $0<\rho<1$, put $w=u+\rho(1/2-u)$. The natural-coordinate kernels satisfy $m_{11}(u,w)=M_{\rm left}(H(u),H(w))$ and $k_{\rm det}(u,w)=K_{\rm factored}(H(u),H(w))$.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionInteriorRatioBridge.lean#L15-L23

import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_correction_minors
import Definitions.Def_GeneralCK_statement

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural

theorem GeneralCK.Correction.Natural.kernel_eq_actual_ratio {u rho : ℝ} (hu : 0 < u) (hhalf : 0 < 1/2-u)
    (hr : 0 < rho) (hr1 : rho < 1) :
    m11 u (u+rho*(1/2-u)) = Mleft (H u) (H (u+rho*(1/2-u))) ∧
    kdet u (u+rho*(1/2-u)) = Kfactored (H u) (H (u+rho*(1/2-u))) := by sorry
