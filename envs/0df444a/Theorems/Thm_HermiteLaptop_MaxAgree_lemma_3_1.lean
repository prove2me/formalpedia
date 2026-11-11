-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_lemma_3_1
-- name    : HermiteLaptop.MaxAgree.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:18:22.379255+00:00
-- url     : https://prove2.me/theorems/433533d5-b99c-4d3a-885f-15b4e42e88a7
-- title:
--   Lemma 3.1 — Hermite coefficients of the argmax indicator as one-dimensional integrals
-- statement:
--   Let $\alpha=(\alpha_1,\dots,\alpha_k)\in\mathbb N_0^k$ and $J_a(x)=\int_{-\infty}^x\varphi(y)h_a(y)\,dy$. Then
--   $$\hat f_1(\alpha)=\int_{-\infty}^{\infty}\varphi(x)h_{\alpha_1}(x)\prod_{q=2}^kJ_{\alpha_q}(x)\,dx,\tag{13}$$
--   and
--   $$J_0(x)=\Phi(x),\qquad J_a(x)=-\frac{\varphi(x)h_{a-1}(x)}{\sqrt a}\quad(a\ge1).\tag{14}$$
--   This reduces each $k$-dimensional coefficient to a single one-dimensional integral.
--
--   **Formalization Note.** The first coordinate is index `0`, so $\hat f_1$ is `hermCoeff ⟨0, hk⟩`, and the product in (13) is over the other coordinates.
--
--   Differences from the source:
--   - encoding: α ∈ ℕ₀^k (with a first coordinate α_1) → k ≥ 1 as a hypothesis; reason: α_1 and f_1 exist only for k ≥ 1
--   - encoding: ∫_{−∞}^{x} and ∫_{−∞}^{∞} → Lebesgue integrals over Set.Iic x and over ℝ; reason: the integrands are integrable
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 18 (PDF 21), Lemma 3.1

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_OneDim

namespace HermiteLaptop.MaxAgree

/-- Lemma 3.1: `f̂_1(α) = ∫ φ(x) h_{α_1}(x) Π_{q=2}^{k} J_{α_q}(x) dx` (13), and (14)
`J_0 = Φ`, `J_a(x) = −φ(x) h_{a−1}(x)/√a` for `a ≥ 1`. -/
theorem lemma_3_1 (k : ℕ) (hk : 1 ≤ k) (α : Fin k → ℕ) :
    hermCoeff (⟨0, hk⟩ : Fin k) α =
      (∫ x, phi x * ∏ q : Fin k, (if q.val = 0 then hNorm (α q) x else Jint (α q) x)) ∧
    (∀ x : ℝ, Jint 0 x = Phi x) ∧
    ∀ a : ℕ, 1 ≤ a → ∀ x : ℝ, Jint a x = -(phi x * hNorm (a - 1) x) / Real.sqrt a := by sorry

end HermiteLaptop.MaxAgree
