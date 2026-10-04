-- Prove2me | Theorems.Thm_OnlineRandomization_Restart_rh_finite
-- name    : OnlineRandomization.Restart.rh_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:36:27.669016+00:00
-- url     : https://prove2.me/theorems/b0a657e7-babd-40f3-89eb-858db03efce7
-- title:
--   Proof of Theorem 4.1, p. 17 — in a local game with finitely many requests, $R_H$ is finite
-- statement:
--   Let $F$ be a request-answer game with a finite request set $R$ and a finite nonempty answer set $A$, and suppose $F$ is local: for every $h > 0$ only finitely many request sequences $r$ have $c(r) \le h$. Then for every real number $H$ the set
--
--   $$R_H = \{ r : c(r') \le H \text{ for every proper prefix } r' \ne r \text{ of } r \}$$
--
--   is finite.
--
--   This is the finiteness behind the paper's claim that the algorithm $A_H$ is a finite table that can be computed in advance; the restart algorithm only consults $A_H$ on $R_H$.
--
--   **Formalization Note** The page credits "the locality property"; finiteness of $R$ is also needed, since a nonempty sequence in $R_H$ is a sequence of cost at most $H$ followed by one arbitrary request. The page cites monotonicity only for the effective listing of $R_H$, which is not formalized. $H$ is any real number, positive or not. Costs are real-valued (the paper allows $+\infty$).
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 17, §4, proof of Theorem 4.1, sentence 3

import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_GameProperties
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm

namespace OnlineRandomization.Restart

/-- §4, proof of Theorem 4.1, p. 17: by locality (and finiteness of the request set `R`),
`R_H` is a finite set, for every real `H`. -/
theorem rh_finite {R A : Type*} [Finite R] [Fintype A] [Nonempty A] (F : Game R A)
    (hloc : IsLocal F) (H : ℝ) :
    {r : List R | InRH F H r}.Finite := by sorry

end OnlineRandomization.Restart
