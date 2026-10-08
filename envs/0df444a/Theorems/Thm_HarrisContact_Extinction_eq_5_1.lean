-- Prove2me | Theorems.Thm_HarrisContact_Extinction_eq_5_1
-- name    : HarrisContact.Extinction.eq_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:48:04.827529+00:00
-- url     : https://prove2.me/theorems/0cb52686-ad60-43c2-ab5c-f9bd1195e439
-- title:
--   (5.1), p. 976 — p_t(ξ) is non-increasing in t and p_∞(ξ) is its limit
-- statement:
--   Let $\{\xi_t\}$ be a contact process on $Z_d$ ($d\ge1$, $\mu\ge0$, $\lambda_0=0$, $\lambda_1,\dots,\lambda_{2d}\ge0$) and, for a finite set $\xi$, let $p_t(\xi)=P_\xi\{\xi_t\neq\varnothing\}$ be its survival probability up to time $t$. Then $t\mapsto p_t(\xi)$ is non-increasing on $[0,\infty)$, and
--   $$p_\infty(\xi)=\lim_{t\to\infty}p_t(\xi).$$
--
--   Harris defines $p_\infty(\xi)$ as this limit, noting that it exists because $p_t(\xi)\downarrow$ in $t$; the statement identifies the infimum used in the model with the page's limit.
--
--   **Formalization Note** $p_t(\xi)=1-P_t(\xi,\varnothing)$ and $p_\infty(\xi)=\inf_{t\ge0}p_t(\xi)$, both in $[0,\infty]$; time runs over $t\ge0$. Stated for finite $\xi$ only; for infinite $\xi$ the page notes $p_t(\xi)=1$.
-- source:
--   Harris (Ann. Probab. 2, 1974), (5.1), p. 976

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- (5.1) (p. 976): p_t(ξ) is non-increasing in t, and p_∞(ξ) = lim_{t→∞} p_t(ξ). -/
theorem eq_5_1 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ : Config d) :
    Antitone (fun t : ℝ≥0 => surv μ lam (t : ℝ) ξ) ∧
      Tendsto (fun t : ℝ≥0 => surv μ lam (t : ℝ) ξ) atTop (𝓝 (survInf μ lam ξ)) := by sorry

end HarrisContact.Extinction
