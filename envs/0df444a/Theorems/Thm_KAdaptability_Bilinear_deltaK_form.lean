-- Prove2me | Theorems.Thm_KAdaptability_Bilinear_deltaK_form
-- name    : KAdaptability.Bilinear.deltaK_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:05:56.848891+00:00
-- url     : https://prove2.me/theorems/157cfa93-1d44-46d0-ad50-5957b01e0d59
-- title:
--   Proof of Theorem 5 — the objective of (6_ε) as a minimum over Δ_K(ℓ)
-- statement:
--   Consider an instance of the two-stage robust binary program with uncertainty set $\Xi=\{\xi:A\xi\le b\}$ nonempty and bounded, $\epsilon>0$, and a decision $(x,\{y^k\}_{k\in\mathcal K})\in\mathcal X\times\mathcal Y^K$. Let $\Xi_\epsilon(\ell)$ be the approximate uncertainty sets of problem $(6_\epsilon)$ and $\Delta_K(\ell)=\{\lambda\in\mathbb R^K_+:e^\top\lambda=1,\ \lambda_k=0\ \forall k:\ell_k\neq0\}$. Then the objective function of $(6_\epsilon)$ satisfies
--   $$\varphi_\epsilon(x,\{y^k\})=\sup_{\ell\in\mathcal L}\ \sup_{\xi\in\Xi_\epsilon(\ell)}\Big[\xi^\top Cx+\inf_{\lambda\in\Delta_K(\ell)}\sum_{k\in\mathcal K}\lambda_k\,\xi^\top Qy^k\Big],$$
--   and $\Delta_K(\ell)=\emptyset$ if and only if $\ell>0$, i.e. $\ell\in\mathcal L_+$.
--
--   The step replaces the minimum over the policies that satisfy all constraints by a minimum of a linear function over a face of the simplex, the first move toward a min-max exchange.
--
--   **Formalization Note** Values are in the extended reals; an infimum over the empty set is $+\infty$ (matching the paper's convention for $\ell\in\mathcal L_+$), a supremum over the empty set is $-\infty$.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec8 (PDF p. 42), Proof of Theorem 5, first display

import Definitions.Def_KAdaptability_Bilinear_Program7

open Matrix

namespace KAdaptability.Bilinear

open Problem

/-- **Proof of Theorem 5, first display** (p. ec8). The objective function of (6_ε) is identical to
`max_{ℓ∈ℒ} max_{ξ∈Ξ_ε(ℓ)} [ξ⊤Cx + min_{λ∈Δ_K(ℓ)} Σ_{k∈𝒦} λ_k · ξ⊤Qy^k]`
(in `EReal`; an infimum over the empty set is `⊤`, a supremum over the empty set is `⊥`),
and `Δ_K(ℓ) = ∅` if and only if `ℓ > 0`, i.e. `ℓ ∈ ℒ₊`. -/
theorem deltaK_form {N M L nQ R K : ℕ} (P : Problem N M L nQ R) (ε : ℝ) (hε : 0 < ε)
    (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (hd : P.IsDecision x y) :
    P.obj6Eps ε x y =
      (⨆ ℓ : Fin K → Fin (L + 1), ⨆ ξ ∈ P.XiEps ε x y ℓ,
        (((P.firstCost ξ x : ℝ) : EReal) +
          ⨅ lam ∈ DeltaK ℓ, ((∑ k, lam k * P.secondCost ξ (y k) : ℝ) : EReal))) ∧
    ∀ ℓ : Fin K → Fin (L + 1), DeltaK ℓ = ∅ ↔ ℓ ∈ LPlus K L := by sorry

end KAdaptability.Bilinear
