-- Prove2me | Theorems.Thm_GivenDegreeSeq_Interior_gf_continuousOn
-- name    : GivenDegreeSeq.Interior.gf_continuousOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:29.517987+00:00
-- url     : https://prove2.me/theorems/e1769514-f2c6-4cd0-b71d-f4da7d110ba0
-- title:
--   $G_f$ is continuous on $[0,1]$ for $f\in D'[0,1]$
-- statement:
--   Let $f\in D'[0,1]$. Then the function
--   $$x\mapsto G_f(x)=\int_x^1\min\{f(y),x\}\,dy+x^2-\int_0^x f(y)\,dy$$
--   is continuous on $[0,1]$.
--
--   Continuity of $G_f$ is used in the proof of Proposition 1.2 to pass from pointwise positivity of $G_f$ on $(0,1]$ to uniform statements under small perturbations of $f$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 23, proof of Proposition 1.2

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_DPrime

namespace GivenDegreeSeq.Interior

/-- Proof of Proposition 1.2, p. 23: for `f ∈ D′[0,1]`, `G_f(x)` is continuous as a function of
`x ∈ [0,1]`. -/
theorem gf_continuousOn (f : ℝ → ℝ) (hf : InDprime f) :
    ContinuousOn (Gf f) (Set.Icc 0 1) := by sorry

end GivenDegreeSeq.Interior
