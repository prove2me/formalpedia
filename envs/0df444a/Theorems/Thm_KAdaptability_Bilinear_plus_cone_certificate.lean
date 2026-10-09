-- Prove2me | Theorems.Thm_KAdaptability_Bilinear_plus_cone_certificate
-- name    : KAdaptability.Bilinear.plus_cone_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:06:03.854986+00:00
-- url     : https://prove2.me/theorems/c3d5dafc-ca70-4e63-894f-d922522f3f49
-- title:
--   Proof of Theorem 5 — Ξ_ε(ℓ) = ∅ for ℓ ∈ ℒ₊ iff a dual cone certificate with value ≤ −1 exists
-- statement:
--   In the setting of problem $(6_\epsilon)$ (uncertainty set $\Xi$ nonempty and bounded, $\epsilon>0$), fix a decision $(x,\{y^k\})\in\mathcal X\times\mathcal Y^K$ and an index $\ell\in\mathcal L_+$, so that $\ell_k\neq0$ for every $k$. Then
--   $$\Xi_\epsilon(\ell)=\{\xi:\ A\xi\le b,\ [Tx+Wy^k]_{\ell_k}\ge[H\xi]_{\ell_k}+\epsilon\ \ \forall k\in\mathcal K\}=\emptyset$$
--   if and only if there exist $\alpha\in\mathbb R^R_+$ and $\gamma\in\mathbb R^K_+$ with
--   $$A^\top\alpha+\sum_{k\in\mathcal K}H_{\ell_k}\gamma_k=0\qquad\text{and}\qquad b^\top\alpha+\sum_{k\in\mathcal K}\big([Tx+Wy^k]_{\ell_k}-\epsilon\big)\gamma_k\le-1,$$
--   where $H_{\ell_k}$ is the $\ell_k$-th row of $H$ as a column vector.
--
--   This is exactly the second block of constraints of problem (7).
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), pp. ec9–ec10 (PDF pp. 43–44), Proof of Theorem 5, the ℒ₊ constraints

import Definitions.Def_KAdaptability_Bilinear_Program7

open Matrix

namespace KAdaptability.Bilinear

open Problem

/-- **Proof of Theorem 5, `ℒ₊` emptiness by a cone certificate** (pp. ec9–ec10). For `ℓ ∈ ℒ₊`,
`Ξ_ε(ℓ) = {ξ : Aξ ≤ b, [Tx + Wy^k]_{ℓ_k} ≥ [Hξ]_{ℓ_k} + ε ∀k ∈ 𝒦}` is empty if and only if there
are `α ∈ ℝ^R_+`, `γ ∈ ℝ^K_+` with `A⊤α + Σ_k H_{ℓ_k}γ_k = 0` and
`b⊤α + Σ_k ([Tx + Wy^k]_{ℓ_k} − ε)γ_k ≤ −1` (the `ℒ₊` block of (7)). -/
theorem plus_cone_certificate {N M L nQ R K : ℕ} (P : Problem N M L nQ R) (ε : ℝ) (hε : 0 < ε)
    (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (hd : P.IsDecision x y)
    (ℓ : Fin K → Fin (L + 1)) (hℓ : ℓ ∈ LPlus K L) :
    P.XiEps ε x y ℓ = ∅ ↔ ∃ (α : Fin R → ℝ) (γ : Fin K → ℝ), P.PlusBlock ε x y ℓ α γ := by sorry

end KAdaptability.Bilinear
