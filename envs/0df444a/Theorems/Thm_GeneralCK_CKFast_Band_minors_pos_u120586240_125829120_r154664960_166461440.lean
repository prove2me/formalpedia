-- Prove2me | Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u120586240_125829120_r154664960_166461440
-- name    : GeneralCK.CKFast.Band.minors_pos_u120586240_125829120_r154664960_166461440
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-09-27T06:28:31.874439+00:00
-- url     : https://prove2.me/theorems/ae671d95-fd6d-431f-8993-a3727e90d2d4
-- title:
--   Correction minors positive on $u\in[23/160,3/20]$, $\rho\in[59/320,127/640]$ (R-B2)
-- statement:
--   Positivity of both correction-Hessian minors on the parameter box
--   $$u\in[23/160,3/20],\qquad \rho\in[59/320,127/640],\qquad \rho<1,$$
--   namely, with $w=u+\rho(1/2-u)$ and $H$ the binary entropy in bits,
--   $$0<M_{\mathrm{left}}\big(H(u),H(w)\big)\quad\text{and}\quad 0<M_{\det}\big(H(u),H(w)\big).$$
--   This box is one piece of the correction band R-B2 of the general Courtade–Kumar proof, the input `hC2`, which is `ActualRatioFamilyOn (1/10) (1/5) (1/10) 1`. The band pieces assemble into that input.
--
--   The statement has exactly the shape of the source's per-cell certificates `actual_minors_positive` (Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931, 2026; https://github.com/dpwoodru/general-courtade-kumar-lean). It is proved here by the computing checker `GeneralCK.CKFast.tree_sound`, over 16 kernel-checked cells.
-- source:
--   Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (2026); band statement: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA5/Bands.lean

import Definitions.Def_GeneralCK_CKFast_eval
import Definitions.Def_GeneralCK_correction_minors

theorem GeneralCK.CKFast.Band.minors_pos_u120586240_125829120_r154664960_166461440 : ∀ u rho : ℝ, u ∈ Set.Icc (23/160 : ℝ) (3/20 : ℝ) →
    rho ∈ Set.Icc (59/320 : ℝ) (127/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by sorry
