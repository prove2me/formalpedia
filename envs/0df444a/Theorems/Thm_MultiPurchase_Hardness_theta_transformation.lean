-- Prove2me | Theorems.Thm_MultiPurchase_Hardness_theta_transformation
-- name    : MultiPurchase.Hardness.theta_transformation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:55.196787+00:00
-- url     : https://prove2.me/theorems/f458fc24-5525-42b8-82b4-dd1035d6875e
-- title:
--   Proof of Theorem 1, App. p. 5 — with r₀ > κ and κ/2 > r₁ > ⋯ > r_m > 0, θij = qij/(ri + rj − κ) turns (7) into the Compare-Step
-- statement:
--   Let $G$ and $Q=(q_{ij})_{0\le i,j\le m}$ be as in problem (7). Choose numbers $\kappa,r_0,r_1,\dots,r_m$ with
--   $$r_0>\kappa\qquad\text{and}\qquad \frac{\kappa}{2}>r_1>r_2>\dots>r_m>0,$$
--   and let $\theta_{ij}=q_{ij}/(r_i+r_j-\kappa)$ for $0\le i,j\le m$. Then
--   1. $\theta_{ij}\ge 0$ for all $i,j$;
--   2. $\theta_{ii}=0$ for all $i$;
--   3. $\theta_{ij}(r_i+r_j-\kappa)=q_{ij}$ for all $i\neq j$.
--
--   With $\hat r_{ij}=r_i+r_j$ for $i\ne j$, the Compare-Step objective $\sum_i\sum_j\theta_{ij}x^C_ix^C_j(\hat r_{ij}-\kappa)$ therefore equals the objective of (7), and the weights $\theta$ are admissible (nonnegative) BundleMVL-2 parameters.
--
--   **Formalization Note** The page's chain $\kappa/2>r_1>\dots>r_m>0$ is stated as: $0<r_i<\kappa/2$ for every node $i$, and $r$ strictly decreasing on the nodes. Only $0<r_i<\kappa/2$ is needed for the conclusion; the ordering is kept because the page states it. The hub is index `0 : Fin (m+1)` and node $i$ is index `i.succ`.
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, proof of Theorem 1, Appendix p. 5 (PDF 37), 'We can also see that problem (7) can be transformed into an equivalent Compare-step problem …'

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model

namespace MultiPurchase.Hardness

/-- Proof of Theorem 1, Appendix p. 5: choose `κ, r₀, r₁, …, r_m` with `r₀ > κ` and
`κ/2 > r₁ > r₂ > ⋯ > r_m > 0`, and let `θᵢⱼ = qᵢⱼ/(rᵢ + rⱼ − κ)`, `0 ≤ i, j ≤ m`. Then every
`θᵢⱼ` is nonnegative, `θᵢᵢ = 0`, and `θᵢⱼ (rᵢ + rⱼ − κ) = qᵢⱼ` for `i ≠ j`, so that the
objective of the Compare-Step equals the objective of (7). -/
theorem theta_transformation {m : ℕ} (G : SimpleGraph (Fin m)) (kappa : ℚ) (r : Fin (m + 1) → ℚ)
    (h0 : kappa < r 0) (hhalf : ∀ i : Fin m, r i.succ < kappa / 2)
    (hpos : ∀ i : Fin m, 0 < r i.succ) (hanti : StrictAnti fun i : Fin m => r i.succ) :
    (∀ i j, 0 ≤ redTheta G kappa r i j) ∧ (∀ i, redTheta G kappa r i i = 0) ∧
    (∀ i j, i ≠ j → redTheta G kappa r i j * (r i + r j - kappa) = hubQ G i j) := by sorry

end MultiPurchase.Hardness
