-- Prove2me | Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u75497472_79691776_r159907840_184156160
-- name    : GeneralCK.CKFast.Band.minors_pos_u75497472_79691776_r159907840_184156160
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-09-27T10:49:17.18379+00:00
-- url     : https://prove2.me/theorems/cced6b25-a340-48d4-ac3f-5f0c7410a820
-- title:
--   Correction minors positive on $u\in[9/100,19/200]$, $\rho\in[61/320,281/1280]$ (R-B1)
-- statement:
--   Positivity of both correction-Hessian minors on the parameter box
--   $$u\in[9/100,19/200],\qquad \rho\in[61/320,281/1280],\qquad \rho<1,$$
--   namely, with $w=u+\rho(1/2-u)$ and $H$ the binary entropy in bits,
--   $$0<M_{\mathrm{left}}\big(H(u),H(w)\big)\quad\text{and}\quad 0<M_{\det}\big(H(u),H(w)\big).$$
--   This box is one piece of the correction band R-B1 of the general Courtade–Kumar proof, the input `hC1`, which is `ActualRatioFamilyOn (1/50) (1/10) (3/40) 1`. The band pieces assemble into that input.
--
--   The statement has exactly the shape of the source's per-cell certificates `actual_minors_positive` (Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931, 2026; https://github.com/dpwoodru/general-courtade-kumar-lean). It is proved here by the computing checker `GeneralCK.CKFast.tree_sound`, over 16 kernel-checked cells.
-- source:
--   Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (2026); band statement: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA5/Bands.lean

import Definitions.Def_GeneralCK_CKFast_eval
import Definitions.Def_GeneralCK_correction_minors

theorem GeneralCK.CKFast.Band.minors_pos_u75497472_79691776_r159907840_184156160 : ∀ u rho : ℝ, u ∈ Set.Icc (9/100 : ℝ) (19/200 : ℝ) →
    rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by sorry
