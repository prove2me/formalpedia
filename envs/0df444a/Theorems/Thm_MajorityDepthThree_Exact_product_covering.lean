-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_product_covering
-- name    : MajorityDepthThree.Exact.product_covering
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:17.55912+00:00
-- url     : https://prove2.me/theorems/34a6da17-1d49-436f-8dd1-dfa96037d38d
-- title:
--   Fact 5.13 — feasibility, optimality and cost under products
-- statement:
--   Let $\mathcal A_1,\mathcal A_2$ be finite set systems on disjoint finite grounds $V_1,V_2$, and let $f_1,f_2$ be feasible covering weights at the fixed Section 5 parameters. Define $\mathcal A_1\otimes\mathcal A_2$ by unions and $(f_1\otimes f_2)(S)=f_1(S\cap V_1)f_2(S\cap V_2)$. Then
--
--   $$f_1\otimes f_2\text{ is feasible},\qquad \operatorname{cost}(f_1\otimes f_2)=\operatorname{cost}(f_1)\operatorname{cost}(f_2).$$
--
--   If both original weights are optimal, their product is optimal as well. Empty families are included. The full product statement supplies the behavior of disjoint components, including exact optimization rather than only a feasible upper bound.
--
--   Differences from the source:
--   - encoding: A finite ground set V and its subsets → Finite subsets V of a variable type, with finite families of subsets; reason: Every source instance has this representation; all assignments and ambient isolated variables are retained
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.15, Fact 5.13

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact

theorem product_covering {α : Type} [DecidableEq α] (V₁ V₂ : Finset α)
    (A₁ A₂ : Family α) (hA₁ : ∀ S ∈ A₁, S ⊆ V₁) (hA₂ : ∀ S ∈ A₂, S ⊆ V₂)
    (hd : Disjoint V₁ V₂) (f₁ f₂ : Weight α)
    (hf₁ : CoverFeasible A₁ q f₁) (hf₂ : CoverFeasible A₂ q f₂) :
    CoverFeasible (productFamily A₁ A₂) q (productWeight V₁ V₂ f₁ f₂) ∧
    (CoverOptimal A₁ r q f₁ → CoverOptimal A₂ r q f₂ →
      CoverOptimal (productFamily A₁ A₂) r q (productWeight V₁ V₂ f₁ f₂)) ∧
    cost (productFamily A₁ A₂) r (productWeight V₁ V₂ f₁ f₂) =
      cost A₁ r f₁ * cost A₂ r f₂ := by sorry

end MajorityDepthThree.Exact
