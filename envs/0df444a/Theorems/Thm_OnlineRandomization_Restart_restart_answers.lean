-- Prove2me | Theorems.Thm_OnlineRandomization_Restart_restart_answers
-- name    : OnlineRandomization.Restart.restart_answers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:36:43.559454+00:00
-- url     : https://prove2.me/theorems/2b23c665-2d14-4cf7-a594-a9a73971e6f5
-- title:
--   Proof of Theorem 4.1, p. 18 — the restart algorithm answers $A_H(r(1)), \dots, A_H(r(t))$
-- statement:
--   Let $F$ be a request-answer game with finite nonempty answer set, $H$ a real number, $A_H$ a deterministic online algorithm and $r$ a request sequence with restart segments $r(1), \dots, r(t)$. Then $r$ is the concatenation of its segments, and the restart algorithm built from $A_H$ answers $r$ with the concatenation of $A_H$'s answers to the segments, each taken from scratch:
--
--   $$r = r(1)\, r(2) \cdots r(t), \qquad \mathrm{Restart}(r) = A_H(r(1))\, A_H(r(2)) \cdots A_H(r(t)).$$
--
--   This is the precise sense in which the algorithm "starts over, as if it had not received any previous requests" whenever the request sequence leaves $R_H$; it is the identity through which the cost of the restart algorithm is compared with the costs of $A_H$ on the segments.
--
--   **Formalization Note** The identity holds for every $H$ and every $A_H$, with no hypothesis on the game. Answer sequences are Lean lists and the concatenation is `List.flatten`.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 18, §4, proof of Theorem 4.1, second paragraph, sentences 2-4

import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm

namespace OnlineRandomization.Restart

/-- p. 18: `r` is the concatenation `r(1) r(2) ⋯ r(t)` of its segments, and the answer
sequence of the restart algorithm on `r` is `A_H(r(1)), A_H(r(2)), …, A_H(r(t))`: on each
segment it answers exactly as `A_H` answers that segment from scratch. -/
theorem restart_answers {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (AH : DetAlg R A) (r : List R) :
    (segments F H r).flatten = r ∧
      (restart F H AH).answers r = ((segments F H r).map AH.answers).flatten := by sorry

end OnlineRandomization.Restart
