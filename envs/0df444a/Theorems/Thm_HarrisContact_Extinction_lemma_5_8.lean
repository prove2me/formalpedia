-- Prove2me | Theorems.Thm_HarrisContact_Extinction_lemma_5_8
-- name    : HarrisContact.Extinction.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:50:32.414347+00:00
-- url     : https://prove2.me/theorems/eea2a5a4-d3b8-4044-a850-df9652382f14
-- title:
--   Lemma 5.8, p. 978 — if λ_k ≤ min_{j ≥ k} λ'_j, then p_t ≤ p'_t and m_t ≤ m'_t
-- statement:
--   Let $\{\xi_t\}$ and $\{\xi'_t\}$ be contact processes on $Z_d$ ($d\ge1$) with the same recovery rate $\mu\ge0$ and infection rates $\lambda_0=0,\lambda_1,\dots,\lambda_{2d}\ge0$ and $\lambda'_0=0,\lambda'_1,\dots,\lambda'_{2d}\ge0$ respectively. Suppose
--   $$\lambda_k\le\min_{j:\,k\le j\le 2d}\lambda'_j,\qquad k=1,\dots,2d .$$
--   Then for every finite $\xi$ and every $t\ge0$,
--   $$p_t(\xi)\le p'_t(\xi)\qquad\text{and}\qquad m_t(\xi)\le m'_t(\xi),$$
--   where $p_t$, $m_t$ are the survival probability and expected size of $\{\xi_t\}$ and $p'_t$, $m'_t$ those of $\{\xi'_t\}$.
--
--   This comparison lemma lets a contact process be dominated by one with simpler rates; it is the first step of the proof of Theorem 7.1.
--
--   **Formalization Note** The minimum ranges over $j\le 2d$, the only indices that occur. $m_t(\xi)=\sum_\eta P_t(\xi,\eta)|\eta|$ takes values in $[0,\infty]$. Stated for finite $\xi$ (the page says $\xi\in\Xi$).
-- source:
--   Harris (Ann. Probab. 2, 1974), Lemma 5.8, p. 978

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- Lemma 5.8 (p. 978): if λ_k ≤ min_{j ≥ k} λ'_j for k = 1, …, 2d, then p_t ≤ p'_t and
m_t ≤ m'_t. -/
theorem lemma_5_8 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam lam' : ℕ → ℝ) (hμ : 0 ≤ μ)
    (h0 : lam 0 = 0) (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (h0' : lam' 0 = 0) (hlam' : ∀ k, k ≤ 2 * d → 0 ≤ lam' k)
    (hcmp : ∀ k j : ℕ, 1 ≤ k → k ≤ j → j ≤ 2 * d → lam k ≤ lam' j) :
    ∀ t : ℝ, 0 ≤ t → ∀ ξ : Config d,
      surv μ lam t ξ ≤ surv μ lam' t ξ ∧ meanSize μ lam t ξ ≤ meanSize μ lam' t ξ := by sorry

end HarrisContact.Extinction
