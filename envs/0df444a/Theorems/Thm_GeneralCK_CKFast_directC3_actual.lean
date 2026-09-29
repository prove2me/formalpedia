-- Prove2me | Theorems.Thm_GeneralCK_CKFast_directC3_actual
-- name    : GeneralCK.CKFast.directC3_actual
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-09-28T17:55:09.144703+00:00
-- url     : https://prove2.me/theorems/5a54d5d2-1844-44c7-ae48-37ad02ceb62b
-- title:
--   Correction chart direct C3: $0<M_{\mathrm{left}}$ and $0<M_{\det}$ for $u\in[1/5,3/10]$, $\rho\in[3/20,1)$
-- statement:
--   **Direct C3 chart of the general Courtade–Kumar proof (chart owner `directC3`).** For all
--   $$u\in[1/5,3/10],\qquad \rho\in[3/20,1],\qquad \rho<1,$$
--   and with $w=u+\rho\,(1/2-u)$ and $H$ the binary entropy in bits, both correction-Hessian minors are positive:
--   $$0<M_{\mathrm{left}}\big(H(u),H(w)\big)\quad\text{and}\quad 0<M_{\det}\big(H(u),H(w)\big).$$
--   This is the strict-positivity form of the chart owner `directC3 : SignsOnBox (1/5) (3/10) (3/20) 1` of the source development (`CKLaneA3X.directC3`). The source's lemma `ratioSigns_of_positive` turns it into the sign statement consumed by `orderedTriangle_signs_of_charts` in the proof of the correction fields `correctionLeft` / `correctionDet`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). The source proves this chart by monolithic Taylor-model checks (lane A3X). Here it is proved with 14,218 cells of the computing checker `GeneralCK.CKFast.tree_sound` (917 chunk theorems joined along the cover).
-- source:
--   Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (2026); chart owner: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Owners.lean (directC3) and browse/CKLaneA5/ChartOwnersAsm.lean

import Definitions.Def_GeneralCK_CKFast_eval
import Definitions.Def_GeneralCK_correction_minors

theorem GeneralCK.CKFast.directC3_actual : ∀ ⦃u rho : ℝ⦄, u ∈ Set.Icc (1/5 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by sorry
