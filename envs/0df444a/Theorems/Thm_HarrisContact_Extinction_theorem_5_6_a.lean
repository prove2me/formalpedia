-- Prove2me | Theorems.Thm_HarrisContact_Extinction_theorem_5_6_a
-- name    : HarrisContact.Extinction.theorem_5_6_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:48:08.853336+00:00
-- url     : https://prove2.me/theorems/5872dd44-4840-441c-a806-2892efac880a
-- title:
--   Theorem 5.6(a), p. 977 — if λ_k ↑ in k, the contact process is increasing: p_t(ξ) ≤ p_t(ξ ∪ η)
-- statement:
--   Let $\{\xi_t\}$ be a contact process on $Z_d$ ($d\ge1$, $\mu\ge0$, $\lambda_0=0$, $\lambda_1,\dots,\lambda_{2d}\ge0$) whose infection rates are non-decreasing, $\lambda_0\le\lambda_1\le\dots\le\lambda_{2d}$. Then the process is **increasing** in the sense of (5.2): for all finite $\xi,\eta\subset Z_d$ and all $t\ge0$,
--   $$p_t(\xi)\le p_t(\xi\cup\eta).$$
--
--   Starting from more infected sites never lowers the probability of survival up to time $t$. This is the first of the paper's comparison results.
--
--   **Formalization Note** "$\lambda_k\uparrow$ in $k$" is monotonicity on $k=0,\dots,2d$, the only indices that occur. The page states (5.2) for arbitrary $\xi,\eta\in\Xi$; it is stated here for finite sets, the state space of the chain model (for infinite sets $p_t=1$ by p. 976).
-- source:
--   Harris (Ann. Probab. 2, 1974), Theorem 5.6(a), p. 977; definition (5.2), p. 976

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- Theorem 5.6(a) (p. 977): if λ_k ↑ in k, the contact process is increasing, (5.2). -/
theorem theorem_5_6_a {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (hmono : MonotoneOn lam (Set.Iic (2 * d))) :
    ∀ t : ℝ, 0 ≤ t → ∀ ξ η : Config d, surv μ lam t ξ ≤ surv μ lam t (ξ ∪ η) := by sorry

end HarrisContact.Extinction
