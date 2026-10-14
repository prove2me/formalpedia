-- Prove2me | Theorems.Thm_GMCPBandit_Regret_lemma_EC_10_1
-- name    : GMCPBandit.Regret.lemma_EC_10_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:33:50.912976+00:00
-- url     : https://prove2.me/theorems/c4b7423a-4bac-4e52-bf1d-5245b60d6280
-- title:
--   Lemma EC.10 (1), p. ec20 — |𝔼(R_i|x,β^true) − 𝔼(R_i|x,β^MCP)| ≤ R_max e^{σ₂x_max‖Δ‖₁}σ₂x_max‖Δ‖₁
-- statement:
--   Work in the model of §3 under Assumptions A.1 and A.5, and suppose moreover that $|f'(r\mid\eta)|\le\sigma_2$ for $r\in[-R_{\max},R_{\max}]$ and $|\eta|\le bx_{\max}$. Let $x\in\mathcal X$ be a covariate, $i\in\mathcal K$ a decision and $\beta^{MCP}_i$ any feasible estimate, $\|\beta^{MCP}_i\|_1\le b$. Then, with $\Delta=\beta^{MCP}_i-\beta^{true}_i$,
--   $$\big|\mathbb E(R_i\mid x,\beta^{true}_i)-\mathbb E(R_i\mid x,\beta^{MCP}_i)\big|\le R_{\max}\,e^{\sigma_2x_{\max}\|\Delta\|_1}\,\sigma_2x_{\max}\|\Delta\|_1,$$
--   where $\mathbb E(R\mid x,\beta)=\mu(x^\top\beta)$.
--
--   This is the Lipschitz bound that converts parameter estimation error into expected-reward error.
--
--   **Formalization Note** The proof (p. ec20) uses "$|f'|$ bounded by $\sigma_2$ in assumption A.5", while A.5 bounds $|f'|$ by $\sigma$; the printed constant $\sigma_2$ is kept and the bound $|f'|\le\sigma_2$ is added as a hypothesis. The page assumes $x\in U_k$; the statement holds for every $x\in\mathcal X\supseteq U_k$, a harmless strengthening, and A.3 is not needed for it.
-- source:
--   Wang, Wei and Yao, Online Learning and Decision-Making under Generalized Linear Model with High-Dimensional Data, arXiv:1812.02962v1, p. ec20, Lemma EC.10, statement 1

import Mathlib
import Definitions.Def_GMCPBandit_Regret_Model
import Definitions.Def_GMCPBandit_Regret_Algorithm

open MeasureTheory ProbabilityTheory

namespace GMCPBandit.Regret

/-- **Lemma EC.10, statement 1** (p. ec20). Under A.1 and A.5, with the derivative bound
`|f'(r | η)| ≤ σ₂` used by the proof, for every covariate `x`, decision `i` and feasible estimate
`β̂` (`‖β̂‖₁ ≤ b`):
`|𝔼(R_i | x, β_i) − 𝔼(R_i | x, β̂)| ≤ R_max e^{σ₂x_max‖β̂ − β_i‖₁} σ₂ x_max ‖β̂ − β_i‖₁`. -/
theorem lemma_EC_10_1 {d K : ℕ} (𝒳 : Set (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (xmax s Rmax βmin b σ σ2 σ3 : ℝ)
    (hglm : IsGLMFamily ν g Rmax)
    (hA1 : A1 𝒳 β xmax s Rmax βmin b)
    (hA5 : A5 g Rmax b xmax σ σ2 σ3)
    (hf' : ∀ r ∈ Set.Icc (-Rmax) Rmax, ∀ η : ℝ, |η| ≤ b * xmax →
      |deriv (fun η => negLogDens g r η) η| ≤ σ2)
    (x : Fin d → ℝ) (hx : x ∈ 𝒳) (i : Fin K) (βhat : Fin d → ℝ) (hβhat : l1 βhat ≤ b) :
    |meanFn ν g (x ⬝ᵥ β i) - meanFn ν g (x ⬝ᵥ βhat)| ≤
      Rmax * Real.exp (σ2 * xmax * l1 (βhat - β i)) * σ2 * xmax * l1 (βhat - β i) := by sorry

end GMCPBandit.Regret
