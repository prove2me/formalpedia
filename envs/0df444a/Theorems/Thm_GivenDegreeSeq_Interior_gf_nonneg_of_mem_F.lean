-- Prove2me | Theorems.Thm_GivenDegreeSeq_Interior_gf_nonneg_of_mem_F
-- name    : GivenDegreeSeq.Interior.gf_nonneg_of_mem_F
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:53:38.529023+00:00
-- url     : https://prove2.me/theorems/b202b934-16fb-4d66-823a-b18ab98ec05e
-- title:
--   $G_f\ge0$ on $[0,1]$ for every scaling limit $f\in\mathcal F$
-- statement:
--   Let $f\in\mathcal F$, i.e. $f\in D'[0,1]$ is the scaling limit of a sequence of degree sequences. Then
--   $$G_f(x)=\int_x^1\min\{f(y),x\}\,dy+x^2-\int_0^x f(y)\,dy\ \ge\ 0\qquad\text{for all }x\in[0,1].$$
--
--   This is the passage of the Erdős–Gallai inequalities to the limit; it is the necessity half of condition (ii) in Proposition 1.2, in its non-strict form.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 23, proof of Proposition 1.2

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_ScalingLimit

namespace GivenDegreeSeq.Interior

/-- Proof of Proposition 1.2, p. 23: if `f ∈ F` (`f ∈ D′[0,1]` is a scaling limit of degree
sequences), then `G_f(x) ≥ 0` for every `x ∈ [0,1]`. -/
theorem gf_nonneg_of_mem_F (f : ℝ → ℝ) (hf : f ∈ setF) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Gf f x := by sorry

end GivenDegreeSeq.Interior
