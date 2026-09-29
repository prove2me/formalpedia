-- Prove2me | Theorems.Thm_GeneralCK_CKFast_tree_sound
-- name    : GeneralCK.CKFast.tree_sound
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-09-27T04:52:50.185757+00:00
-- url     : https://prove2.me/theorems/8f722ca0-ab22-456f-bd02-93f0f2d4c5fd
-- title:
--   Soundness of the computing correction-band checker: accepted trees give $0<M_{\mathrm{left}}$ and $0<M_{\det}$
-- statement:
--   **Soundness of the computing correction-band checker.** Let $D = 50\cdot 2^{24}$. Let $U_0,U_1,R_0,R_1\in\mathbb Z$, and let $t$ be a guillotine tree of cells with contact brackets such that `treeOK U0 U1 R0 R1 t = true` (a kernel-decidable Boolean test, see the definition `GeneralCK_CKFast_eval`). Then for every
--   $$u \in \left[\tfrac{U_0}{D},\tfrac{U_1}{D}\right],\qquad \rho\in\left[\tfrac{R_0}{D},\tfrac{R_1}{D}\right],\qquad \rho<1,$$
--   and with $w = u + \rho\,(1/2-u)$, both correction-Hessian minors are positive:
--   $$0 < M_{\mathrm{left}}\big(H(u), H(w)\big) \quad\text{and}\quad 0 < M_{\det}\big(H(u), H(w)\big).$$
--   Here $H$ is binary entropy in bits, and $M_{\mathrm{left}}$, $M_{\det}$ are the minors of the correction Hessian (`GeneralCK.Correction`).
--
--   **Role.** This is the single analytic lemma behind the correction-band inputs $h_{C1}$ (R-B1, $u\in[1/50,1/10]$, $\rho\in[3/40,1]$) and $h_{C2}$ (R-B2, $u\in[1/10,1/5]$, $\rho\in[1/10,1]$) of the general Courtade–Kumar proof. Once it is proved, each part of a band is a single `decide +kernel` on a small tree, replacing the source's per-cell certificate modules (17,675 of them, about 36M lines).
--
--   Source of the statement shape: the R-B1/R-B2 cell theorems `actual_minors_positive`, which assert exactly this conclusion on one box each, of Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026), formalized in https://github.com/dpwoodru/general-courtade-kumar-lean.
-- source:
--   Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (2026); cell statement shape: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/LaneRB2OwnerActual.lean#L61-L66

import Definitions.Def_GeneralCK_CKFast_eval
import Definitions.Def_GeneralCK_correction_minors

theorem GeneralCK.CKFast.tree_sound {U0 U1 R0 R1 : ℤ} {t : GeneralCK.CKFast.Tree}
    (ht : GeneralCK.CKFast.treeOK U0 U1 R0 R1 t = true) (u rho : ℝ)
    (hu : u ∈ Set.Icc ((U0 : ℝ) / GeneralCK.CKFast.D) ((U1 : ℝ) / GeneralCK.CKFast.D))
    (hr : rho ∈ Set.Icc ((R0 : ℝ) / GeneralCK.CKFast.D) ((R1 : ℝ) / GeneralCK.CKFast.D))
    (hr1 : rho < 1) :
    0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
    0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by sorry
