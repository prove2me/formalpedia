-- Prove2me | Theorems.Thm_LambdaVaRAmb_Robust_proposition_2
-- name    : LambdaVaRAmb.Robust.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:39.906263+00:00
-- url     : https://prove2.me/theorems/7dafffd2-b36c-4256-90be-fb1adc12e89d
-- title:
--   Proposition 2 — for Λ ∈ ℋ_I, sup_{w∈W} ΛVaR^w = ΛVaR^{w̄} and inf_{w∈W} ΛVaR^{+,w} = ΛVaR^{+,w̲}
-- statement:
--   Let $(\Omega,\mathcal F)$ be a measurable space, let $W$ be a nonempty class of capacities on $\mathcal F$, and write $\overline w=\sup_{w\in W}w$ and $\underline w=\inf_{w\in W}w$ for its upper and lower envelopes. Let $\Lambda:\mathbb R\to(0,1)$ be increasing. Then for every random variable $X$,
--   $$\sup_{w\in W}\Lambda\mathrm{VaR}^w(X)=\Lambda\mathrm{VaR}^{\overline w}(X)\qquad\text{and}\qquad\inf_{w\in W}\Lambda\mathrm{VaR}^{+,w}(X)=\Lambda\mathrm{VaR}^{+,\underline w}(X).$$
--
--   So for increasing $\Lambda$ the worst case of $\Lambda$VaR over a class of capacities is the $\Lambda$VaR under the upper envelope, and the best case of $\Lambda$VaR$^+$ is the $\Lambda$VaR$^+$ under the lower envelope. The paper's Example 1 shows that the first identity fails for decreasing $\Lambda$.
--
--   **Formalization Note** The equalities hold in $[-\infty,\infty]$ (`EReal`). The class $W$ is assumed nonempty: the paper does not say so, but for $W=\emptyset$ the envelopes are not capacities and $\inf_{w\in\emptyset}=+\infty$, so the second identity fails. $X$ is a measurable real function, which covers every domain $\mathcal X$ of random variables the paper allows.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 8, Proposition 2 (with (2)); proof p. 27

import Mathlib
import Definitions.Def_LambdaVaRAmb_Robust_Setting

namespace LambdaVaRAmb.Robust

open MeasureTheory

theorem proposition_2 {Ω : Type*} [MeasurableSpace Ω]
    (W : Set (Set Ω → ℝ)) (hW : W.Nonempty) (hcap : ∀ w ∈ W, IsCapacity w)
    (Λ : ℝ → ℝ) (hΛ : InHI Λ) (X : Ω → ℝ) (hX : Measurable X) :
    (⨆ w ∈ W, LVaR Λ w X) = LVaR Λ (upperCap W) X ∧
      (⨅ w ∈ W, LVaRPlus Λ w X) = LVaRPlus Λ (lowerCap W) X := by sorry

end LambdaVaRAmb.Robust
