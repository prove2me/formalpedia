-- Prove2me | Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u237240320_238551040_r148111360_153681920
-- name    : GeneralCK.CKFast.Band.minors_pos_u237240320_238551040_r148111360_153681920
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-09-28T09:02:47.45824+00:00
-- url     : https://prove2.me/theorems/a3ff6829-3cfd-4f02-bc2c-7ce817acc6d2
-- title:
--   Correction minors positive on $u\in[181/640,91/320]$, $\rho\in[113/640,469/2560]$ (directC3)
-- statement:
--   Positivity of both correction-Hessian minors on the parameter box
--   $$u\in[181/640,91/320],\qquad \rho\in[113/640,469/2560],\qquad \rho<1,$$
--   namely, with $w=u+\rho(1/2-u)$ and $H$ the binary entropy in bits,
--   $$0<M_{\mathrm{left}}\big(H(u),H(w)\big)\quad\text{and}\quad 0<M_{\det}\big(H(u),H(w)\big).$$
--   This box is one piece of the correction band directC3 of the general Courtade–Kumar proof, the input `directC3`, which is `ActualRatioFamilyOn (1/5) (3/10) (3/20) 1`. The band pieces assemble into that input.
--
--   The statement has exactly the shape of the source's per-cell certificates `actual_minors_positive` (Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931, 2026; https://github.com/dpwoodru/general-courtade-kumar-lean). It is proved here by the computing checker `GeneralCK.CKFast.tree_sound`, over 16 kernel-checked cells.
-- source:
--   Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (2026); band statement: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA5/Bands.lean

import Definitions.Def_GeneralCK_CKFast_eval
import Definitions.Def_GeneralCK_correction_minors

theorem GeneralCK.CKFast.Band.minors_pos_u237240320_238551040_r148111360_153681920 : ∀ u rho : ℝ, u ∈ Set.Icc (181/640 : ℝ) (91/320 : ℝ) →
    rho ∈ Set.Icc (113/640 : ℝ) (469/2560 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by sorry
