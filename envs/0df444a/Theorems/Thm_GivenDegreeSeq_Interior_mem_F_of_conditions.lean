-- Prove2me | Theorems.Thm_GivenDegreeSeq_Interior_mem_F_of_conditions
-- name    : GivenDegreeSeq.Interior.mem_F_of_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:25.360883+00:00
-- url     : https://prove2.me/theorems/a6e9eb7d-51fc-45fa-9a55-54f40a27be51
-- title:
--   Conditions (i)–(ii) of Proposition 1.2 imply $f\in\mathcal F$
-- statement:
--   Let $f\in D'[0,1]$ and suppose that
--
--   1. there are constants $c_1>0$ and $c_2<1$ such that $c_1\le f(x)\le c_2$ for all $x\in[0,1]$, and
--   2. for each $x\in(0,1]$,
--   $$\int_x^1\min\{f(y),x\}\,dy+x^2-\int_0^x f(y)\,dy>0.$$
--
--   Then $f\in\mathcal F$: $f$ is the scaling limit of a sequence of degree sequences of simple graphs.
--
--   This is the first half of the sufficiency direction of Proposition 1.2; combined with the stability of (i)–(ii) under small $\|\cdot\|_{1'}$-perturbations it shows that such $f$ lie in the interior of $\mathcal F$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, pp. 23–24, proof of Proposition 1.2

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_ScalingLimit

namespace GivenDegreeSeq.Interior

/-- Proof of Proposition 1.2, pp. 23–24: if `f ∈ D′[0,1]` satisfies (i) `c₁ ≤ f(x) ≤ c₂` on
`[0,1]` for constants `c₁ > 0`, `c₂ < 1`, and (ii) `G_f(x) > 0` for every `x ∈ (0,1]`, then
`f ∈ F`. -/
theorem mem_F_of_conditions (f : ℝ → ℝ) (hf : InDprime f)
    (h₁ : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₂ < 1 ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, c₁ ≤ f x ∧ f x ≤ c₂)
    (h₂ : ∀ x ∈ Set.Ioc (0 : ℝ) 1, 0 < Gf f x) :
    f ∈ setF := by sorry

end GivenDegreeSeq.Interior
