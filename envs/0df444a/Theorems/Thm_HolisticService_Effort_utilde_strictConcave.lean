-- Prove2me | Theorems.Thm_HolisticService_Effort_utilde_strictConcave
-- name    : HolisticService.Effort.utilde_strictConcave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:39.880566+00:00
-- url     : https://prove2.me/theorems/06efc00d-b075-4f5f-9c0d-fc9e334987c2
-- title:
--   Proof of Proposition 1, p. 26 — Ũ(δ) is strictly concave in δ
-- statement:
--   Assume the standing assumptions of the service design model. Then the function
--   $$\tilde{\mathcal U}(\delta) = \mathcal U(\delta, \tilde\pi(\delta))$$
--   is strictly concave on $\mathbb R^n$.
--
--   Strict concavity makes the effort problem a convex program with at most one optimum, which is how Proposition 1 obtains uniqueness of the optimal effort.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), p. 26 (PDF 26), proof of Proposition 1

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

namespace HolisticService.Effort

/-- Proof of Proposition 1, p. 26: `Ũ(δ)` is strictly concave in `δ`. -/
theorem utilde_strictConcave {n : ℕ} (M : Params n) (hS : M.Standing) :
    StrictConcaveOn ℝ Set.univ (Utilde M) := by sorry

end HolisticService.Effort
