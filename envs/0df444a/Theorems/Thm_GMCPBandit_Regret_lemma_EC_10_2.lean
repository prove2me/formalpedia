-- Prove2me | Theorems.Thm_GMCPBandit_Regret_lemma_EC_10_2
-- name    : GMCPBandit.Regret.lemma_EC_10_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:33:35.761154+00:00
-- url     : https://prove2.me/theorems/3c75065e-8d59-4493-8dbf-4b90b68bef7d
-- title:
--   Lemma EC.10 (2), p. ec20 — estimates within min{1/(σ₂x_max), h/(4eσ₂R_max x_max)} keep an h/2 margin on U_i
-- statement:
--   Work in the model of §3 under Assumptions A.1 and A.5, with $|f'(r\mid\eta)|\le\sigma_2$ on $[-R_{\max},R_{\max}]\times[-bx_{\max},bx_{\max}]$ and a margin $h>0$. Let $\hat\beta_k$, $k\in\mathcal K$, be feasible estimates ($\|\hat\beta_k\|_1\le b$) with
--   $$\|\hat\beta_k-\beta^{true}_k\|_1\le\min\Big\{\frac1{\sigma_2x_{\max}},\frac{h}{4e\sigma_2R_{\max}x_{\max}}\Big\}\quad\text{for every }k\in\mathcal K.$$
--   Then for every decision $i$ and every $x\in U_i$,
--   $$\mathbb E(R_i\mid x,\hat\beta_i)\ge\max_{j\ne i}\mathbb E(R_j\mid x,\hat\beta_j)+\frac h2.$$
--
--   This is display (9) of p. 18: on the event that every random-sample estimate is accurate, the optimal decision at $x\in U_i$ is the only member of the shortlist $\Pi_t$.
--
--   **Formalization Note** The printed indices ("$x\in U_k$, $i\in\mathcal K$", "$\beta^{MCP}_k$" on both sides) are read as display (9): $x\in U_i$ and each decision evaluated at its own estimate. As in statement 1, the bound $|f'|\le\sigma_2$ used by the proof is added.
-- source:
--   Wang, Wei and Yao, Online Learning and Decision-Making under Generalized Linear Model with High-Dimensional Data, arXiv:1812.02962v1, p. ec20, Lemma EC.10, statement 2; p. 18, (8)–(9)

import Mathlib
import Definitions.Def_GMCPBandit_Regret_Model
import Definitions.Def_GMCPBandit_Regret_Algorithm

open MeasureTheory ProbabilityTheory

namespace GMCPBandit.Regret

/-- **Lemma EC.10, statement 2** (p. ec20; display (9), p. 18). Under A.1 and A.5, with
`|f'(r | η)| ≤ σ₂` and `h > 0`: if feasible estimates `β̂_k` satisfy
`‖β̂_k − β_k‖₁ ≤ min{1/(σ₂x_max), h/(4eσ₂R_max x_max)}` for every `k ∈ 𝒦`, then for every `x ∈ U_i`,
`𝔼(R_i | x, β̂_i) ≥ max_{j≠i} 𝔼(R_j | x, β̂_j) + h/2`. -/
theorem lemma_EC_10_2 {d K : ℕ} (hK : 2 ≤ K) (𝒳 : Set (Fin d → ℝ)) (ν : Measure ℝ)
    (g : ℝ → ℝ → ℝ) (β : Fin K → Fin d → ℝ) (xmax s Rmax βmin b h σ σ2 σ3 : ℝ)
    (hglm : IsGLMFamily ν g Rmax)
    (hA1 : A1 𝒳 β xmax s Rmax βmin b)
    (hA5 : A5 g Rmax b xmax σ σ2 σ3)
    (hf' : ∀ r ∈ Set.Icc (-Rmax) Rmax, ∀ η : ℝ, |η| ≤ b * xmax →
      |deriv (fun η => negLogDens g r η) η| ≤ σ2)
    (hh : 0 < h)
    (βhat : Fin K → Fin d → ℝ) (hfeas : ∀ k, l1 (βhat k) ≤ b)
    (hclose : ∀ k, l1 (βhat k - β k) ≤
      min (1 / (σ2 * xmax)) (h / (4 * Real.exp 1 * σ2 * Rmax * xmax)))
    (i : Fin K) (x : Fin d → ℝ) (hx : x ∈ optRegion 𝒳 ν g β h i) :
    maxOther ν g βhat x i + h / 2 ≤ meanFn ν g (x ⬝ᵥ βhat i) := by sorry

end GMCPBandit.Regret
