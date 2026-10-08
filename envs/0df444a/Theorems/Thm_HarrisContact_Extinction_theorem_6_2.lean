-- Prove2me | Theorems.Thm_HarrisContact_Extinction_theorem_6_2
-- name    : HarrisContact.Extinction.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:51:29.704323+00:00
-- url     : https://prove2.me/theorems/93b4e0de-0b41-423b-a83b-d85e6af352d4
-- title:
--   Theorem 6.2, p. 979 — if {λ_i} is concave and non-decreasing, λ_0 = 0, then p_t is submodular
-- statement:
--   Let $\{\xi_t\}$ be a contact process on $Z_d$ ($d\ge1$, $\mu\ge0$) whose infection rates $\lambda_0=0,\lambda_1,\dots,\lambda_{2d}\ge0$ are non-decreasing and concave in $i$, that is, $\lambda_{i+1}-\lambda_i$ is non-increasing for $i=0,\dots,2d-1$. Then $p_t$ is **submodular** in the sense of (5.4): for all finite $\xi,\eta\subset Z_d$ and all $t\ge0$,
--   $$p_t(\xi\cup\eta)+p_t(\xi\cap\eta)\le p_t(\xi)+p_t(\eta).$$
--
--   Submodularity says that the gain in survival probability from adding sites diminishes as the set grows. The simplest examples are $\lambda_k=k\lambda_1$ and $\lambda_k=\lambda_1$ for $k\ge1$; the first is the case used in the proof of Theorem 7.1.
--
--   **Formalization Note** Concavity is written as $\lambda_{i+2}-\lambda_{i+1}\le\lambda_{i+1}-\lambda_i$ for $i+2\le2d$. Stated for finite $\xi,\eta$ (the page says arbitrary $\xi,\eta\in\Xi$; for infinite sets $p_t=1$).
-- source:
--   Harris (Ann. Probab. 2, 1974), §6, Theorem 6.2, p. 979; definition (5.4), p. 976

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- Theorem 6.2 (p. 979): if {λ_i : i = 0, …, 2d} is concave and non-decreasing with λ_0 = 0,
then p_t is submodular, (5.4). -/
theorem theorem_6_2 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (hmono : MonotoneOn lam (Set.Iic (2 * d)))
    (hconc : ∀ i : ℕ, i + 2 ≤ 2 * d → lam (i + 2) - lam (i + 1) ≤ lam (i + 1) - lam i) :
    ∀ t : ℝ, 0 ≤ t → ∀ ξ η : Config d,
      surv μ lam t (ξ ∪ η) + surv μ lam t (ξ ∩ η) ≤ surv μ lam t ξ + surv μ lam t η := by sorry

end HarrisContact.Extinction
