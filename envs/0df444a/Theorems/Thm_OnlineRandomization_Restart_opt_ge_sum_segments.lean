-- Prove2me | Theorems.Thm_OnlineRandomization_Restart_opt_ge_sum_segments
-- name    : OnlineRandomization.Restart.opt_ge_sum_segments
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:36:15.448716+00:00
-- url     : https://prove2.me/theorems/27521fcf-231c-4beb-b626-d2a15662b293
-- title:
--   Proof of Theorem 4.1, p. 18 — $c(r) \ge c(r(1)) + \sum_{i=2}^{t} (c(r(i)) - D(F))$
-- statement:
--   Let $F$ be a request-answer game with finite nonempty answer set and let $D$ bound its diameter. For every decomposition of a request sequence $r = r(1)\, r(2) \cdots r(t)$ into $t \ge 1$ consecutive pieces,
--
--   $$c(r) \ge c(r(1)) + \sum_{i=2}^{t} \big(c(r(i)) - D\big).$$
--
--   The off-line optimum loses at most $D$ at each of the $t-1$ cuts. Applied to the segments of the restart algorithm, this is the lower bound on the adversary's cost in the proof of Theorem 4.1.
--
--   **Formalization Note** Stated, in a form equivalent to the page's, as $\sum_{i=1}^t c(r(i)) - (t-1)D \le c(r)$, with $t$ cast to a real number before subtracting $1$. It is stated for every decomposition into consecutive pieces (Lean: `segs` with `segs.flatten = r`, `segs ≠ []`), which includes the restart algorithm's decomposition ($r = $ `(segments F H r).flatten`, by `restart_answers`); this is more general than the page, which uses it only for that decomposition. $D$ is any bound on the diameter; $D = D(F)$ is the page's case.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 18, §4, proof of Theorem 4.1, third paragraph (display)

import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_GameProperties

namespace OnlineRandomization.Restart

/-- p. 18: if `D` bounds the diameter, then for every decomposition of a request sequence into
`t ≥ 1` consecutive pieces `r(1), …, r(t)`,
`c(r(1) ⋯ r(t)) ≥ c(r(1)) + Σ_{i=2}^{t} (c(r(i)) − D)`. -/
theorem opt_ge_sum_segments {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (D : ℝ)
    (hD : DiameterBound F D) (segs : List (List R)) (hsegs : segs ≠ []) :
    (segs.map F.opt).sum - ((segs.length : ℝ) - 1) * D ≤ F.opt segs.flatten := by sorry

end OnlineRandomization.Restart
