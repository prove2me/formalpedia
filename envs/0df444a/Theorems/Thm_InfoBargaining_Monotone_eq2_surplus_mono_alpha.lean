-- Prove2me | Theorems.Thm_InfoBargaining_Monotone_eq2_surplus_mono_alpha
-- name    : InfoBargaining.Monotone.eq2_surplus_mono_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:49.434421+00:00
-- url     : https://prove2.me/theorems/4369e2a8-918d-48ad-8175-02cef274c9f1
-- title:
--   Display (2) and footnote 7, p. 8 — the mean of v is û for every α, and A(α, c) increases in α
-- statement:
--   Let $F$ be the prior with mean $\hat u$, let $v=\alpha w+(1-\alpha)\hat u$ be the posterior mean under the truth-or-noise signal, and let
--   $$A(\alpha,c)=\mathbb E\big[(v-c)^+\big]=\int_c^{\bar v}(v-c)\,dG(v,\alpha)$$
--   be the total ex ante surplus at seller cost $c$. Then:
--
--   1. for every $\alpha\in(0,1)$, the mean of $v$ is $\hat u$;
--   2. for every $c\in\mathbb R$, the map $\alpha\mapsto A(\alpha,c)$ is nondecreasing on $(0,1)$.
--
--   A higher $\alpha$ is a mean-preserving spread of the distribution of $v$ (display (2)), so by footnote 7 the expectation of the convex interim utility $(v-c)^+$ increases with $\alpha$. This is the fact the proof of Proposition 1 uses to show that the buyer's marginal benefit of information grows with its bargaining power.
--
--   **Formalization Note** The mean-preserving-spread property (2) is stated through its consequence for the convex function $v\mapsto(v-c)^+$, the only interim utility the paper applies footnote 7 to; the inequality is weak because the prior may have no density.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 8, display (2) and footnote 7

import Mathlib
import Definitions.Def_InfoBargaining_Monotone_Setting

namespace InfoBargaining.Monotone

open MeasureTheory

/-- Display (2) and footnote 7, p. 8: the posterior mean has mean `û` for every `α`, and a
higher `α` (a mean-preserving spread) raises the ex ante surplus `A(α, c)` of the convex
interim utility `(v - c)⁺`, for every cost `c`. -/
theorem eq2_surplus_mono_alpha (M : Model) :
    (∀ α ∈ Set.Ioo (0 : ℝ) 1, ∫ w, M.postMean α w ∂M.μ = M.uhat) ∧
    ∀ c : ℝ, MonotoneOn (fun α => M.A α c) (Set.Ioo (0 : ℝ) 1) := by sorry

end InfoBargaining.Monotone
