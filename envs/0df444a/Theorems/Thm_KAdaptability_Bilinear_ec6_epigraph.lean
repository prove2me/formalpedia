-- Prove2me | Theorems.Thm_KAdaptability_Bilinear_ec6_epigraph
-- name    : KAdaptability.Bilinear.ec6_epigraph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:05:51.854268+00:00
-- url     : https://prove2.me/theorems/df8f033b-a0ab-4a1d-9890-d93f401c3cd5
-- title:
--   Proof of Theorem 5, (EC.6) — epigraph reformulation of (6_ε)
-- statement:
--   In the setting of problem $(6_\epsilon)$ (uncertainty set $\Xi$ nonempty and bounded, $\epsilon>0$), fix a decision $(x,\{y^k\})\in\mathcal X\times\mathcal Y^K$. Then the objective value of $(6_\epsilon)$ at this decision is the optimal value of the epigraph problem (EC.6):
--   $$\varphi_\epsilon(x,\{y^k\})=\inf\left\{\tau\in\mathbb R:\ \exists\,\lambda(\ell)\in\Delta_K(\ell),\ \ell\in\partial\mathcal L,\ \text{with}\ \begin{array}{ll}\tau\ge\xi^\top Cx+\sum_{k}\lambda_k(\ell)\,\xi^\top Qy^k & \forall\ell\in\partial\mathcal L,\ \forall\xi\in\Xi_\epsilon(\ell)\\ \Xi_\epsilon(\ell)=\emptyset & \forall\ell\in\mathcal L_+\end{array}\right\}.$$
--
--   In particular the objective is $+\infty$ exactly when some $\Xi_\epsilon(\ell)$ with $\ell\in\mathcal L_+$ is nonempty. Optimizing over the decisions gives the equivalence of $(6_\epsilon)$ and (EC.6).
--
--   **Formalization Note** The infimum is taken in the extended reals; the infimum of the empty set is $+\infty$, and if every real $\tau$ qualifies it is $-\infty$.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec8 (PDF p. 42), Proof of Theorem 5, problem (EC.6)

import Definitions.Def_KAdaptability_Bilinear_Program7

open Matrix

namespace KAdaptability.Bilinear

open Problem

/-- **Proof of Theorem 5, (EC.6)** (p. ec8). For every decision `(x, {y^k}) ∈ 𝒳 × 𝒴^K`, the
objective value of (6_ε) equals the infimum of the `τ ∈ ℝ` for which there are
`λ(ℓ) ∈ Δ_K(ℓ)`, `ℓ ∈ ∂ℒ`, with
`τ ≥ ξ⊤Cx + Σ_k λ_k(ℓ) · ξ⊤Qy^k` for all `ℓ ∈ ∂ℒ`, `ξ ∈ Ξ_ε(ℓ)`, and `Ξ_ε(ℓ) = ∅` for all
`ℓ ∈ ℒ₊` (in `EReal`; the infimum of no `τ` is `+∞`). -/
theorem ec6_epigraph {N M L nQ R K : ℕ} (P : Problem N M L nQ R) (ε : ℝ) (hε : 0 < ε)
    (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (hd : P.IsDecision x y) :
    P.obj6Eps ε x y =
      sInf ((fun τ : ℝ => (τ : EReal)) ''
        {τ | ∃ lam : (Fin K → Fin (L + 1)) → Fin K → ℝ,
          (∀ ℓ ∈ LBdry K L, lam ℓ ∈ DeltaK ℓ) ∧
          (∀ ℓ ∈ LBdry K L, ∀ ξ ∈ P.XiEps ε x y ℓ, P.lagCost x y (lam ℓ) ξ ≤ τ) ∧
          ∀ ℓ ∈ LPlus K L, P.XiEps ε x y ℓ = ∅}) := by sorry

end KAdaptability.Bilinear
