-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_lemma_1
-- name    : NonconvexAG.Stoch.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:02.768274+00:00
-- url     : https://prove2.me/theorems/627bbe7b-f9b5-4e30-a39c-ac1be1568c7f
-- title:
--   Lemma 1 — the Γ_k-weighted recursion bound θ_k ≤ Γ_k Σ_{i≤k} η_i/Γ_i
-- statement:
--   Let $\{\alpha_k\}_{k\ge1}$ satisfy $\alpha_1=1$ and $\alpha_k\in(0,1)$ for $k\ge2$, and let $\Gamma_1=1$, $\Gamma_k=(1-\alpha_k)\Gamma_{k-1}$ ($k\ge2$), as in (2.6). If real sequences $\{\theta_k\}_{k\ge0}$ and $\{\eta_k\}_{k\ge1}$ satisfy
--   $$\theta_k\le(1-\alpha_k)\theta_{k-1}+\eta_k,\qquad k=1,2,\dots,$$
--   then for every $k\ge1$
--   $$\theta_k\le\Gamma_k\sum_{i=1}^k\frac{\eta_i}{\Gamma_i}.$$
--
--   This unrolls the one-step recursion of the convex part of the analysis; in the proof of Theorem 3 b) it is applied to $\theta_k=\Psi(x^{ag}_k)-\Psi(x)$.
--
--   **Formalization Note** Sequences are functions on $\mathbb N$ with 1-based indexing; $\theta_0$ is arbitrary (it is multiplied by $1-\alpha_1=0$). $\Gamma$ is the product $\prod_{i=2}^k(1-\alpha_i)$ of the mission's definition file. This statement restates the paper's Lemma 1 locally in this mission, as in the companion missions of the series.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 4, Lemma 1 (2.5)–(2.6)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- Lemma 1 (Ghadimi–Lan, arXiv:1310.3787v1, p. 4): if `α₁ = 1`, `αₖ ∈ (0, 1)` for `k ≥ 2`, and
`θₖ ≤ (1 − αₖ) θₖ₋₁ + ηₖ` for `k ≥ 1` (2.5), then `θₖ ≤ Γₖ Σ_{i=1}^{k} ηᵢ / Γᵢ` for `k ≥ 1`,
with `Γ` as in (2.6). -/
theorem lemma_1 (α : ℕ → ℝ) (hα1 : α 1 = 1) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1)
    (θ η : ℕ → ℝ) (h : ∀ k, 1 ≤ k → θ k ≤ (1 - α k) * θ (k - 1) + η k) :
    ∀ k, 1 ≤ k → θ k ≤ NonconvexAG.Smooth.Gamma α k * ∑ i ∈ Finset.Icc 1 k, η i / NonconvexAG.Smooth.Gamma α i := by sorry

end NonconvexAG.Stoch
