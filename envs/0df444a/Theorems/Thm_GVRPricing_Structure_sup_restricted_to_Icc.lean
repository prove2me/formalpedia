-- Prove2me | Theorems.Thm_GVRPricing_Structure_sup_restricted_to_Icc
-- name    : GVRPricing.Structure.sup_restricted_to_Icc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:45:16.594794+00:00
-- url     : https://prove2.me/theorems/b5dd5aa5-9be1-4ff4-8125-7adb0e15791c
-- title:
--   Proof of Proposition 1 — for $\Delta\ge0$ the supremum in (8) is a maximum over $[0,\lambda^*]$
-- statement:
--   Let $\Lambda$, $r$ and $\lambda^*$ come from a regular demand function, and let $\Delta \ge 0$ be a marginal value. Then the supremum of $r(\lambda) - \lambda\Delta$ over the allowable rates is finite, it can be computed over the compact interval $[0,\lambda^*]$, and it is attained there:
--   $$\sup_{\lambda\in\Lambda}\big[r(\lambda)-\lambda\Delta\big] \;=\; \sup_{\lambda\in[0,\lambda^*]}\big[r(\lambda)-\lambda\Delta\big] \;=\; \max_{\lambda\in[0,\lambda^*]}\big[r(\lambda)-\lambda\Delta\big],$$
--   and some maximizer over $[0,\lambda^*]$ maximizes over all of $\Lambda$.
--
--   This is the first step of the paper's proof of Proposition 1: it reduces the control set in (8) to a compact interval, which is what makes the existence and uniqueness argument work, and it yields $\lambda^*(n,t)\le\lambda^*$.
--
--   **Formalization Note** The paper applies this with $\Delta = J(n,t)-J(n-1,t)$ while assuming that $J$ is nondecreasing in $n$, a fact that is only established later (Theorem 1). Stating it for an arbitrary $\Delta \ge 0$ removes that circularity. The interval $[0,\lambda^*]$ lies in $\Lambda$ because $\Lambda$ is an interval containing $0$ and $\lambda^*$.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1017 (PDF 19), Appendix, Proof of Proposition 1, first paragraph

import Mathlib
import Definitions.Def_GVRPricing_Structure_Model
import Definitions.Def_GVRPricing_Structure_IsHJBSolution

namespace GVRPricing.Structure

/-- Proof of Proposition 1, first paragraph (Gallego–van Ryzin 1994, Appendix, p. 1017): for a
regular demand function and any marginal value `Δ ≥ 0`, the supremum of `r(λ) − λ Δ` over the
allowable rates `Λ` is finite, equals its supremum over `[0, λ*]`, and is attained at a rate in
`[0, λ*]`. -/
theorem sup_restricted_to_Icc (M : Model) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    BddAbove (hamObjective M Δ '' M.Λ) ∧
    sSup (hamObjective M Δ '' M.Λ) = sSup (hamObjective M Δ '' Set.Icc 0 M.lamStar) ∧
    ∃ x ∈ Set.Icc 0 M.lamStar, IsMaxOn (hamObjective M Δ) M.Λ x := by sorry

end GVRPricing.Structure
