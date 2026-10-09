-- Prove2me | Theorems.Thm_KAdaptability_Bilinear_bdry_lp_duality
-- name    : KAdaptability.Bilinear.bdry_lp_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:05:54.134599+00:00
-- url     : https://prove2.me/theorems/e30cba02-19ed-4c68-a187-7ae35162f696
-- title:
--   Proof of Theorem 5 — the ∂ℒ semi-infinite constraint by LP duality
-- statement:
--   In the setting of problem $(6_\epsilon)$ (uncertainty set $\Xi$ nonempty and bounded, $\epsilon>0$), fix a decision $(x,\{y^k\})\in\mathcal X\times\mathcal Y^K$, an index $\ell\in\partial\mathcal L$ and weights $\lambda\in\Delta_K(\ell)$. Consider the linear program
--   $$\max\Big\{\Big[Cx+\sum_{k}\lambda_kQy^k\Big]^\top\xi:\ A\xi\le b,\ \ Tx+Wy^k\le H\xi\ \forall k:\ell_k=0,\ \ [Tx+Wy^k]_{\ell_k}\ge[H\xi]_{\ell_k}+\epsilon\ \forall k:\ell_k\neq0\Big\},$$
--   whose feasible set is $\Xi_\epsilon(\ell)$, and its dual
--   $$\min\Big\{b^\top\alpha-\sum_{k:\ell_k=0}(Tx+Wy^k)^\top\beta^k+\sum_{k:\ell_k\neq0}\big([Tx+Wy^k]_{\ell_k}-\epsilon\big)\gamma_k:\ \alpha,\beta^k,\gamma\ge0,\ A^\top\alpha-\sum_{k:\ell_k=0}H^\top\beta^k+\sum_{k:\ell_k\neq0}H_{\ell_k}\gamma_k=Cx+\sum_k\lambda_kQy^k\Big\}.$$
--   Then:
--
--   1. the two problems have the same optimal value;
--   2. for every $\tau\in\mathbb R$, the semi-infinite constraint $\big[Cx+\sum_k\lambda_kQy^k\big]^\top\xi\le\tau$ for all $\xi\in\Xi_\epsilon(\ell)$ holds if and only if the dual has a feasible solution with objective value at most $\tau$.
--
--   This turns the semi-infinite constraint of (EC.6) for $\ell\in\partial\mathcal L$ into the finite first block of constraints of problem (7).
--
--   **Formalization Note** Optimal values are suprema and infima in the extended reals; if $\Xi_\epsilon(\ell)=\emptyset$ the primal value is $-\infty$, and the statement asserts the dual value is then $-\infty$ too.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec9 (PDF p. 43), Proof of Theorem 5, primal and dual LPs for ℓ ∈ ∂ℒ

import Definitions.Def_KAdaptability_Bilinear_Program7

open Matrix

namespace KAdaptability.Bilinear

open Problem

/-- **Proof of Theorem 5, the `∂ℒ` constraint by LP duality** (p. ec9). Fix `ℓ ∈ ∂ℒ`,
`λ ∈ Δ_K(ℓ)` and `τ ∈ ℝ`.
1. The LP `max {(Cx + Σ_k λ_k Qy^k)⊤ξ : ξ ∈ Ξ_ε(ℓ)}` and its dual
   `min {b⊤α − Σ_{k:ℓ_k=0} (Tx+Wy^k)⊤β^k + Σ_{k:ℓ_k≠0} ([Tx+Wy^k]_{ℓ_k} − ε)γ_k :
   α, β^k, γ ≥ 0, A⊤α − Σ_{k:ℓ_k=0} H⊤β^k + Σ_{k:ℓ_k≠0} H_{ℓ_k}γ_k = Cx + Σ_k λ_k Qy^k}`
   have the same optimal value (in `EReal`; an infeasible primal has value `⊥`).
2. The semi-infinite constraint `(Cx + Σ_k λ_k Qy^k)⊤ξ ≤ τ ∀ξ ∈ Ξ_ε(ℓ)` holds if and only if
   the dual has a feasible solution with objective value at most `τ`. -/
theorem bdry_lp_duality {N M L nQ R K : ℕ} (P : Problem N M L nQ R) (ε : ℝ) (hε : 0 < ε)
    (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (hd : P.IsDecision x y)
    (ℓ : Fin K → Fin (L + 1)) (hℓ : ℓ ∈ LBdry K L)
    (lam : Fin K → ℝ) (hlam : lam ∈ DeltaK ℓ) :
    (⨆ ξ ∈ P.XiEps ε x y ℓ, ((P.costVec x y lam ⬝ᵥ ξ : ℝ) : EReal)) =
      (⨅ (α : Fin R → ℝ) (β : Fin K → Fin L → ℝ) (γ : Fin K → ℝ)
          (_ : 0 ≤ α ∧ (∀ k, 0 ≤ β k) ∧ 0 ≤ γ ∧
            P.dualLhsBdry ℓ α β γ = P.costVec x y lam),
        ((P.dualObjBdry ε x y ℓ α β γ : ℝ) : EReal)) ∧
    ∀ τ : ℝ, (∀ ξ ∈ P.XiEps ε x y ℓ, P.costVec x y lam ⬝ᵥ ξ ≤ τ) ↔
      ∃ (α : Fin R → ℝ) (β : Fin K → Fin L → ℝ) (γ : Fin K → ℝ),
        P.DualBdry ε x y ℓ lam τ α β γ := by sorry

end KAdaptability.Bilinear
