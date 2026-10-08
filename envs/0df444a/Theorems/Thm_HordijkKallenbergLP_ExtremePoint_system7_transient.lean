-- Prove2me | Theorems.Thm_HordijkKallenbergLP_ExtremePoint_system7_transient
-- name    : HordijkKallenbergLP.ExtremePoint.system7_transient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:57:17.038826+00:00
-- url     : https://prove2.me/theorems/bfc273bf-f57b-4254-a898-aaeb010a5c59
-- title:
--   Proof of Theorem 10, p. 362 — a solution of (7) has y_i = (β^T D)_i on the transient states
-- statement:
--   Let $P$ be a stochastic matrix on a finite set, $D$ its deviation matrix, and $T$ its set of transient states. If row vectors $x,y$ solve system (7), $x^T(I-P)=0$ and $x^T+y^T(I-P)=\beta^T$, then
--   $$
--   y_i=(\beta^TD)_i,\qquad i\in T.
--   $$
--
--   In the proof of Theorem 10 this shows that two feasible points with the zero pattern of a pure representative agree on the transient states.
--
--   **Formalization Note.** A state is transient when it is not recurrent in the sense of the published `IsRecurrent`: some state accessible from it does not lead back to it.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 362, proof of Theorem 10

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_ExtremePoint_Model
open Matrix MarkovDecisionProcesses BlackwellDiscreteDP.NearOne

namespace HordijkKallenbergLP.ExtremePoint

/-- **Proof of Theorem 10, p. 362 (unnumbered): solutions of (7) on the transient states.** Let
`P` be a Markov matrix and `T` its set of transient states. If `x, y` solve system (7),
`x^T(I − P) = 0`, `x^T + y^T(I − P) = β^T`, then `y_i = (β^T D)_i` for every `i ∈ T`.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 362, proof of Theorem 10
("Then y_i = (β^T D)_i, i ∈ T.").

**Formalization Note.** A state `i` is transient when it is not recurrent in the sense of the
published `IsRecurrent` (some state accessible from `i` does not lead back to `i`). Row vectors
act by `vecMul`; `D` is the published `deviationMatrix`. -/
theorem system7_transient {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : IsMarkovMatrix P) (β x y : n → ℝ) (h3 : x ᵥ* (1 - P) = 0)
    (h4 : x + y ᵥ* (1 - P) = β) (i : n) (hi : ¬ IsRecurrent P i) :
    y i = (β ᵥ* deviationMatrix P) i := by sorry

end HordijkKallenbergLP.ExtremePoint
