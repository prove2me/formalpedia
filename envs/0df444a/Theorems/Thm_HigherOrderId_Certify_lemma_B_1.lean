-- Prove2me | Theorems.Thm_HigherOrderId_Certify_lemma_B_1
-- name    : HigherOrderId.Certify.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:19:08.098497+00:00
-- url     : https://prove2.me/theorems/f9bc0c0f-649e-4b5a-b707-f2bf5ed56a8e
-- title:
--   Lemma B.1 — value moments raise the centered channel's Fisher information by at most 1 + 2α² ≤ 3/2
-- statement:
--   Let $d\ge10$, $0<\alpha\le1/2$, $\sigma>0$, and consider a design $(x_e,n_e)_{e\le E}$ that is centered, $\sum_ex_e=0$, has balanced allocation ($n_e=n_{e'}\ge1$ for all $e,e'$), and satisfies $\|x_e\|_2\le\alpha$. Let $I_{\mathrm{grad}}$ and $I_{\mathrm{full}}$ be the Fisher information operators for $(b,Q)$ from, respectively, the gradient releases and the joint value–gradient releases in (52). Then, in the Loewner order on $\mathbb R^d\times S^d_0$,
--   $$I_{\mathrm{grad}}\preceq I_{\mathrm{full}}\preceq(1+2\alpha^2)I_{\mathrm{grad}}\preceq\tfrac32I_{\mathrm{grad}}.$$
--
--   The value moments therefore change the information of the centered channel by at most a universal factor, which lets the lower bound of Theorem 5.2 be proved from the gradient channel.
--
--   Differences from the source:
--   - encoding: Fisher information operators I_grad, I_full and the Loewner order ⪯ → the quadratic forms Σ_e (n_e/σ²)‖h + Hx_e‖² and that plus Σ_e (n_e/σ²)(hᵀx_e + x_eᵀHx_e/2)², compared at every (h, H) ∈ ℝ^d × S^d_0; reason: the Fisher information of a Gaussian experiment with known covariance and mean linear in the parameter is AᵀΣ⁻¹A; the Loewner order of symmetric operators is the order of their quadratic forms
--   - encoding: the allocation is balanced → all n_e are equal and at least 1; reason: allocations n_e ≥ 1 is the standing assumption of §B.1
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 21, Lemma B.1 (PDF p. 22)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Release
import Definitions.Def_HigherOrderId_Certify_Fisher

namespace HigherOrderId.Certify

/-- Lemma B.1 (value moments preserve the centered-channel spectrum). For a centered design
(`Σ_e x_e = 0`) with balanced allocation and `‖x_e‖₂ ≤ α ≤ 1/2`, the Fisher information
operators of the gradient releases and of the joint value–gradient releases (52) for `(b, Q)`
satisfy `I_grad ⪯ I_full ⪯ (1 + 2α²) I_grad ⪯ (3/2) I_grad`, written as the comparison of their
quadratic forms at every perturbation `(h, H) ∈ ℝ^d × S^d_0`. -/
theorem lemma_B_1 (d E : ℕ) (D : Design d E) (α σ : ℝ) (hd : 10 ≤ d) (hα0 : 0 < α)
    (hα1 : α ≤ 1 / 2) (hσ : 0 < σ) (hcent : ∑ e, D.x e = 0)
    (hbal : ∀ e e', D.n e = D.n e') (hpos : ∀ e, 1 ≤ D.n e)
    (hnorm : ∀ e, Real.sqrt (∑ i, D.x e i ^ 2) ≤ α)
    (h : Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (hH : IsSymZeroDiag H) :
    gradFisher D σ h H ≤ fullFisher D σ h H ∧
    fullFisher D σ h H ≤ (1 + 2 * α ^ 2) * gradFisher D σ h H ∧
    (1 + 2 * α ^ 2) * gradFisher D σ h H ≤ (3 / 2) * gradFisher D σ h H := by sorry

end HigherOrderId.Certify
