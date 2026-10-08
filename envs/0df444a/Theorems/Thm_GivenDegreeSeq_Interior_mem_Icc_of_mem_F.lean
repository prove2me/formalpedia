-- Prove2me | Theorems.Thm_GivenDegreeSeq_Interior_mem_Icc_of_mem_F
-- name    : GivenDegreeSeq.Interior.mem_Icc_of_mem_F
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:25.69857+00:00
-- url     : https://prove2.me/theorems/b61ed198-11ca-45da-954c-58de5b386ddd
-- title:
--   Every scaling limit $f\in\mathcal F$ takes values in $[0,1]$
-- statement:
--   Let $f\in\mathcal F$. Then
--   $$0\le f(x)\le 1\qquad\text{for all }x\in[0,1].$$
--
--   Degrees of a graph on $n$ vertices lie in $\{0,\dots,n-1\}$, so normalized degrees lie in $[0,1]$; this is the necessity half of condition (i) in Proposition 1.2 in its non-strict form.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 23, proof of Proposition 1.2

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_ScalingLimit

namespace GivenDegreeSeq.Interior

/-- Proof of Proposition 1.2, p. 23: every `f ∈ F` takes values in `[0,1]` on `[0,1]`. -/
theorem mem_Icc_of_mem_F (f : ℝ → ℝ) (hf : f ∈ setF) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ∈ Set.Icc (0 : ℝ) 1 := by sorry

end GivenDegreeSeq.Interior
