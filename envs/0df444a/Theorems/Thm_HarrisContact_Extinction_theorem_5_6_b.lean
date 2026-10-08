-- Prove2me | Theorems.Thm_HarrisContact_Extinction_theorem_5_6_b
-- name    : HarrisContact.Extinction.theorem_5_6_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:48:15.522894+00:00
-- url     : https://prove2.me/theorems/e904a585-78de-451c-92bc-03c30dac7903
-- title:
--   Theorem 5.6(b), p. 977 — if also λ_k/k ↓, the contact process is subadditive: p_t(ξ ∪ η) ≤ p_t(ξ) + p_t(η)
-- statement:
--   Let $\{\xi_t\}$ be a contact process on $Z_d$ ($d\ge1$, $\mu\ge0$, $\lambda_0=0$, $\lambda_1,\dots,\lambda_{2d}\ge0$) with $\lambda_k$ non-decreasing in $k$ and $\lambda_k/k$ non-increasing in $k\ge1$. Then the process is **subadditive** in the sense of (5.3): for all finite $\xi,\eta\subset Z_d$ and all $t\ge0$,
--   $$p_t(\xi\cup\eta)\le p_t(\xi)+p_t(\eta).$$
--
--   Subadditivity is what allows survival from a large set to be bounded by survival from single sites; it is the property used in the display preceding Theorem 7.1.
--
--   **Formalization Note** The monotonicity is on $k=0,\dots,2d$ and the ratio condition on $k=1,\dots,2d$. Stated for finite $\xi,\eta$ (the page says arbitrary $\xi,\eta\in\Xi$; for infinite sets $p_t=1$).
-- source:
--   Harris (Ann. Probab. 2, 1974), Theorem 5.6(b), p. 977; definition (5.3), p. 976

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- Theorem 5.6(b) (p. 977): if λ_k ↑ in k and λ_k/k ↓ in k ≥ 1, the contact process is
subadditive, (5.3). -/
theorem theorem_5_6_b {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (hmono : MonotoneOn lam (Set.Iic (2 * d)))
    (hratio : AntitoneOn (fun k : ℕ => lam k / k) (Set.Icc 1 (2 * d))) :
    ∀ t : ℝ, 0 ≤ t → ∀ ξ η : Config d,
      surv μ lam t (ξ ∪ η) ≤ surv μ lam t ξ + surv μ lam t η := by sorry

end HarrisContact.Extinction
