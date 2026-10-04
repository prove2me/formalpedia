-- Prove2me | Theorems.Thm_OnlineRandomization_Restart_segment_opt_ge
-- name    : OnlineRandomization.Restart.segment_opt_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:36:39.047981+00:00
-- url     : https://prove2.me/theorems/c1d771bd-4669-433e-966b-dcaac1cba25d
-- title:
--   Proof of Theorem 4.1, p. 18 — every segment but the last has optimum $c(i) \ge H$
-- statement:
--   Let $F$ be a monotone request-answer game with finite nonempty answer set, $H$ a real number and $r$ a request sequence with restart segments $r(1), \dots, r(t)$. Then
--
--   $$c(i) = c(r(i)) \ge H, \qquad i = 1, 2, \dots, t-1.$$
--
--   Each segment other than the last was closed because appending the next request left $R_H$; together with monotonicity this forces its off-line optimum to be at least $H$. This is the inequality that charges the additive losses of the restart algorithm to the off-line optimum.
--
--   **Formalization Note** In Lean the segments other than the last are `(segments F H r).dropLast`. Monotonicity is used through its consequence that $c$ does not decrease along prefixes. The statement holds for every real $H$ and every request sequence (vacuously when $t \le 1$).
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 18, §4, proof of Theorem 4.1, fourth paragraph, sentence 2

import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_GameProperties
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm

namespace OnlineRandomization.Restart

/-- p. 18: for a monotone game, every segment `r(i)` except the last one, `i = 1, …, t − 1`,
has off-line optimum `c(i) = c(r(i)) ≥ H`. -/
theorem segment_opt_ge {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A)
    (hmono : IsMonotone F) (H : ℝ) (r : List R) :
    ∀ s ∈ (segments F H r).dropLast, H ≤ F.opt s := by sorry

end OnlineRandomization.Restart
