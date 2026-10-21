-- Prove2me | Theorems.Thm_HiringLP_SimLower_expMinPois_div_antitone
-- name    : HiringLP.SimLower.expMinPois_div_antitone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:45.538134+00:00
-- url     : https://prove2.me/theorems/94fab932-5e1f-4ed5-a11a-1ebafc93989b
-- title:
--   App. D.5, p. ec16 — E[min{Pois(x), k}]/x is decreasing in x
-- statement:
--   For every $k\in\mathbb N$, the function
--   $$x\ \longmapsto\ \frac{\mathbb E[\min\{\mathrm{Pois}(x),k\}]}{x}$$
--   is non-increasing on $(0,\infty)$.
--
--   In the proof of Lemma 13 this fact drives the Poisson splitting argument and lets the total mass $sM$ of the truncated solution be replaced by $sk$, using $M\le k$.
--
--   **Formalization Note** The paper's "decreasing" is read as non-increasing (`AntitoneOn` on $(0,\infty)$); for $k=0$ the function is identically $0$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. ec16 (PDF p. 48), App. D.5 (proof of Lemma 13), sentence after the splitting display

import Mathlib
import Definitions.Def_HiringLP_SimLower_PoissonRatio

namespace HiringLP.SimLower

/-- App. D.5, p. ec16: `E[min{Pois(x), k}]/x` is decreasing in `x > 0`. -/
theorem expMinPois_div_antitone (k : ℕ) :
    AntitoneOn (fun x : ℝ => expMinPois x k / x) (Set.Ioi 0) := by sorry

end HiringLP.SimLower
