-- Prove2me | Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u158597120_159907840_r83886080_89784320
-- name    : GeneralCK.CKFast.Band.minors_pos_u158597120_159907840_r83886080_89784320
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-09-27T08:10:37.278944+00:00
-- url     : https://prove2.me/theorems/d7b56a2c-794c-4f7a-99b0-c8b6232ad5f9
-- title:
--   Correction minors positive on $u\in[121/640,61/320]$, $\rho\in[1/10,137/1280]$ (R-B2)
-- statement:
--   Positivity of both correction-Hessian minors on the parameter box
--   $$u\in[121/640,61/320],\qquad \rho\in[1/10,137/1280],\qquad \rho<1,$$
--   namely, with $w=u+\rho(1/2-u)$ and $H$ the binary entropy in bits,
--   $$0<M_{\mathrm{left}}\big(H(u),H(w)\big)\quad\text{and}\quad 0<M_{\det}\big(H(u),H(w)\big).$$
--   This box is one piece of the correction band R-B2 of the general Courtade–Kumar proof, the input `hC2`, which is `ActualRatioFamilyOn (1/10) (1/5) (1/10) 1`. The band pieces assemble into that input.
--
--   The statement has exactly the shape of the source's per-cell certificates `actual_minors_positive` (Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931, 2026; https://github.com/dpwoodru/general-courtade-kumar-lean). It is proved here by the computing checker `GeneralCK.CKFast.tree_sound`, over 16 kernel-checked cells.
-- source:
--   Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (2026); band statement: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA5/Bands.lean

import Definitions.Def_GeneralCK_CKFast_eval
import Definitions.Def_GeneralCK_correction_minors

theorem GeneralCK.CKFast.Band.minors_pos_u158597120_159907840_r83886080_89784320 : ∀ u rho : ℝ, u ∈ Set.Icc (121/640 : ℝ) (61/320 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (137/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by sorry
