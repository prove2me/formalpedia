-- Prove2me | Theorems.Thm_KAdaptability_Bilinear_minmax_exchange
-- name    : KAdaptability.Bilinear.minmax_exchange
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:06:03.690287+00:00
-- url     : https://prove2.me/theorems/6cb0c3de-64f2-4928-8390-5f64354f6487
-- title:
--   Proof of Theorem 5 — min-max exchange over ∂ℒ
-- statement:
--   In the setting of problem $(6_\epsilon)$ (uncertainty set $\Xi$ nonempty and bounded, $\epsilon>0$), fix a decision $(x,\{y^k\})\in\mathcal X\times\mathcal Y^K$ and suppose $\Xi_\epsilon(\ell)=\emptyset$ for every $\ell\in\mathcal L_+$. Then the objective $\varphi_\epsilon(x,\{y^k\})$ of $(6_\epsilon)$ equals each of the three expressions
--   $$\max_{\ell\in\partial\mathcal L}\ \max_{\xi\in\Xi_\epsilon(\ell)}\Big[\xi^\top Cx+\min_{\lambda\in\Delta_K(\ell)}\sum_{k}\lambda_k\,\xi^\top Qy^k\Big],$$
--   $$\max_{\ell\in\partial\mathcal L}\ \min_{\lambda\in\Delta_K(\ell)}\ \max_{\xi\in\Xi_\epsilon(\ell)}\Big[\xi^\top Cx+\sum_{k}\lambda_k\,\xi^\top Qy^k\Big],$$
--   $$\min_{\lambda(\ell)\in\Delta_K(\ell),\ \ell\in\partial\mathcal L}\ \max_{\ell\in\partial\mathcal L}\ \max_{\xi\in\Xi_\epsilon(\ell)}\Big[\xi^\top Cx+\sum_{k}\lambda_k(\ell)\,\xi^\top Qy^k\Big].$$
--
--   The second equality is the classical min-max theorem, applicable because $\Delta_K(\ell)$ is nonempty for every $\ell\in\partial\mathcal L$; the third lets the weights depend on $\ell$.
--
--   **Formalization Note** Maxima and minima are suprema and infima in the extended reals; a supremum over an empty set $\Xi_\epsilon(\ell)$ is $-\infty$. In the third expression the infimum ranges over families $\ell\mapsto\lambda(\ell)$ with $\lambda(\ell)\in\Delta_K(\ell)$ for $\ell\in\partial\mathcal L$ (values at $\ell\in\mathcal L_+$ are unconstrained and unused).
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec8 (PDF p. 42), Proof of Theorem 5, second to fourth displays

import Definitions.Def_KAdaptability_Bilinear_Program7

open Matrix

namespace KAdaptability.Bilinear

open Problem

/-- **Proof of Theorem 5, min-max exchange on `∂ℒ`** (p. ec8). If `Ξ_ε(ℓ) = ∅` for all
`ℓ ∈ ℒ₊`, the objective of (6_ε) equals each of
1. `max_{ℓ∈∂ℒ} max_{ξ∈Ξ_ε(ℓ)} [ξ⊤Cx + min_{λ∈Δ_K(ℓ)} Σ_k λ_k · ξ⊤Qy^k]`,
2. `max_{ℓ∈∂ℒ} min_{λ∈Δ_K(ℓ)} max_{ξ∈Ξ_ε(ℓ)} [ξ⊤Cx + Σ_k λ_k · ξ⊤Qy^k]`,
3. `min_{λ(ℓ)∈Δ_K(ℓ), ℓ∈∂ℒ} max_{ℓ∈∂ℒ} max_{ξ∈Ξ_ε(ℓ)} [ξ⊤Cx + Σ_k λ_k(ℓ) · ξ⊤Qy^k]`,
all in `EReal` (a maximum over an empty `Ξ_ε(ℓ)` is `⊥`). -/
theorem minmax_exchange {N M L nQ R K : ℕ} (P : Problem N M L nQ R) (ε : ℝ) (hε : 0 < ε)
    (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (hd : P.IsDecision x y)
    (hplus : ∀ ℓ ∈ LPlus K L, P.XiEps ε x y ℓ = ∅) :
    P.obj6Eps ε x y =
      (⨆ ℓ ∈ LBdry K L, ⨆ ξ ∈ P.XiEps ε x y ℓ,
        (((P.firstCost ξ x : ℝ) : EReal) +
          ⨅ lam ∈ DeltaK ℓ, ((∑ k, lam k * P.secondCost ξ (y k) : ℝ) : EReal))) ∧
    P.obj6Eps ε x y =
      (⨆ ℓ ∈ LBdry K L, ⨅ lam ∈ DeltaK ℓ, ⨆ ξ ∈ P.XiEps ε x y ℓ,
        ((P.lagCost x y lam ξ : ℝ) : EReal)) ∧
    P.obj6Eps ε x y =
      (⨅ (lam : (Fin K → Fin (L + 1)) → Fin K → ℝ) (_ : ∀ ℓ ∈ LBdry K L, lam ℓ ∈ DeltaK ℓ),
        ⨆ ℓ ∈ LBdry K L, ⨆ ξ ∈ P.XiEps ε x y ℓ, ((P.lagCost x y (lam ℓ) ξ : ℝ) : EReal)) := by sorry

end KAdaptability.Bilinear
