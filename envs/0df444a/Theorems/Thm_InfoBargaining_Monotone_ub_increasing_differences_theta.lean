-- Prove2me | Theorems.Thm_InfoBargaining_Monotone_ub_increasing_differences_theta
-- name    : InfoBargaining.Monotone.ub_increasing_differences_theta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:41.700928+00:00
-- url     : https://prove2.me/theorems/a4d1aa5b-58a8-4b03-9001-1a475033038b
-- title:
--   Proof of Proposition 1, p. 30 — ∂²U_b/∂θ_b∂α ≥ 0: U_b has increasing differences in (α, θ_b)
-- statement:
--   Fix the seller's cost $c\in\mathbb R$ and write $U_b(\alpha;\theta_b)=\theta_b A(\alpha,c)-k(\alpha)$ for the buyer's objective (6). Then $U_b$ has increasing differences in $(\alpha,\theta_b)$ on $[\underline\alpha,\bar\alpha]\times(0,1)$: for all $\theta_b<\theta_b'$ in $(0,1)$, the map
--   $$\alpha\ \longmapsto\ U_b(\alpha;\theta_b')-U_b(\alpha;\theta_b)$$
--   is nondecreasing on $[\underline\alpha,\bar\alpha]$.
--
--   This is the discrete form of the paper's sign condition $\partial^2U_b/\partial\theta_b\partial\alpha=-\int_c^{\bar v}\partial G(v,\alpha)/\partial\alpha\,dv\ge0$. Together with Topkis's theorem it gives the first part of Proposition 1.
--
--   **Formalization Note** Increasing differences is the platform definition `Supermodularity.Monotonicity.IncreasingDifferencesOn` with the decision variable $\alpha$ first and the parameter $\theta_b$ second. The paper writes "positive"; the weak form is what Topkis's theorem needs, and the difference is $0$ when $c$ lies above the support of $v$.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 30, Appendix, proof of Proposition 1, second sentence

import Mathlib
import Definitions.Def_InfoBargaining_Monotone_Setting
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn

namespace InfoBargaining.Monotone

/-- Proof of Proposition 1, p. 30, second sentence: for every cost `c`, the buyer's
objective `U_b` has increasing differences in `(α, θ_b)` on `[αlo, αhi] × (0, 1)`
(the cross-partial `∂²U_b/∂θ_b∂α` is nonnegative). -/
theorem ub_increasing_differences_theta (M : Model) (c : ℝ) :
    Supermodularity.Monotonicity.IncreasingDifferencesOn
      (fun α θb => M.Ub θb c α) (Set.Icc M.αlo M.αhi ×ˢ Set.Ioo (0 : ℝ) 1) := by sorry

end InfoBargaining.Monotone
