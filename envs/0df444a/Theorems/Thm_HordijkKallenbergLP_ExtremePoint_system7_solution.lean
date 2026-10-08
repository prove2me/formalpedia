-- Prove2me | Theorems.Thm_HordijkKallenbergLP_ExtremePoint_system7_solution
-- name    : HordijkKallenbergLP.ExtremePoint.system7_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:57:37.049164+00:00
-- url     : https://prove2.me/theorems/362b197b-b42c-43a4-9a5b-2a2caa238c7d
-- title:
--   Proof of Theorem 10, p. 362 — every solution of (7) has x^T = β^T P* and y^T = β^T D + y^T P*
-- statement:
--   Let $P$ be a stochastic matrix on a finite set, $P^*$ its Cesàro limit matrix and $D=(I-P+P^*)^{-1}-P^*$ its deviation matrix, and let $\beta$ be any vector. If row vectors $x,y$ solve the system
--   $$
--   x^T(I-P)=0,\qquad x^T+y^T(I-P)=\beta^T, \qquad (7)
--   $$
--   then
--   $$
--   x^T=\beta^TP^*\qquad\text{and}\qquad y^T=\beta^TD+y^TP^*.
--   $$
--
--   In the proof of Theorem 10 this pins down the $x$-part of any feasible point sharing the zero pattern of a pure representative, and reduces the $y$-part to a vector that is invariant under $P$ up to a known term.
--
--   **Formalization Note.** Row vectors are functions acting by `vecMul`. $P^*$ and $D$ are the published `limitMatrix` and `deviationMatrix`; their identities are Blackwell's Lemma 1(a), 1(d) and are not hypotheses here.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 362, proof of Theorem 10, (7)

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_ExtremePoint_Model
open Matrix MarkovDecisionProcesses BlackwellDiscreteDP.NearOne

namespace HordijkKallenbergLP.ExtremePoint

/-- **Proof of Theorem 10, p. 362 (unnumbered): every solution of system (7).** Let `P` be a
Markov matrix with limit matrix `P*` and deviation matrix `D = (I − P + P*)⁻¹ − P*`. If row
vectors `x, y` solve
`x^T(I − P) = 0`, `x^T + y^T(I − P) = β^T`  (7),
then `x^T = β^T P*` and `y^T = β^T D + y^T P*`.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 362, proof of Theorem 10, display (7) and the two lines after it.

**Formalization Note.** Row vectors are functions `n → ℝ` acting by `vecMul` (`x ᵥ* P` is
`x^T P`). Neither positivity of `β` nor any MDP structure is needed. `limitMatrix` and
`deviationMatrix` are the published Blackwell definitions; their identities
(`PP* = P*P = P*P* = P*`, `(I − P)D = I − P*`, `P*D = DP* = 0`) are Blackwell's Lemma 1(a), 1(d)
(Hordijk–Kallenberg's Theorem 2), not hypotheses here. -/
theorem system7_solution {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : IsMarkovMatrix P) (β x y : n → ℝ) (h3 : x ᵥ* (1 - P) = 0)
    (h4 : x + y ᵥ* (1 - P) = β) :
    x = β ᵥ* limitMatrix P ∧ y = β ᵥ* deviationMatrix P + y ᵥ* limitMatrix P := by sorry

end HordijkKallenbergLP.ExtremePoint
