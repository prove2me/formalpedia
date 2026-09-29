-- Prove2me | Theorems.Thm_GeneralCK_CKFast_hC1_actual
-- name    : GeneralCK.CKFast.hC1_actual
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-09-27T11:43:47.553835+00:00
-- url     : https://prove2.me/theorems/8f0a39d6-e136-4a23-99c1-b150060697be
-- title:
--   Correction band R-B1: $0<M_{\mathrm{left}}$ and $0<M_{\det}$ for $u\in[1/50,1/10]$, $\rho\in[3/40,1)$ ($h_{C1}$)
-- statement:
--   **Correction band R-B1 of the general Courtade–Kumar proof (input `hC1`).** For all
--   $$u\in[1/50,1/10],\qquad \rho\in[3/40,1],\qquad \rho<1,$$
--   and with $w=u+\rho\,(1/2-u)$ and $H$ the binary entropy in bits, both correction-Hessian minors are positive:
--   $$0<M_{\mathrm{left}}\big(H(u),H(w)\big)\quad\text{and}\quad 0<M_{\det}\big(H(u),H(w)\big).$$
--   This is exactly `ActualRatioFamilyOn (1/50) (1/10) (3/40) 1` of the source development, unfolded (`ActualRatioMinorsPositive u ρ` is the conjunction above). It is the band input `hC1` consumed by `orderedTriangle_signs_of_charts` in the proof of the correction fields `correctionLeft` / `correctionDet`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). The source proves this with 5,891 certificate cells. Here it is proved with 3,310 cells of the computing checker `GeneralCK.CKFast.tree_sound`.
-- source:
--   Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (2026); statement: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA5/Bands.lean (band2_actual / band1_actual) and browse/GeneralCK/LaneRB2OwnerActual.lean#L61-L66 (unfolded form)

import Definitions.Def_GeneralCK_CKFast_eval
import Definitions.Def_GeneralCK_correction_minors

theorem GeneralCK.CKFast.hC1_actual : ∀ ⦃u rho : ℝ⦄, u ∈ Set.Icc (1/50 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by sorry
