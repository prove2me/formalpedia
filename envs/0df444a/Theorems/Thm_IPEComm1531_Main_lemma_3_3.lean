-- Prove2me | Theorems.Thm_IPEComm1531_Main_lemma_3_3
-- name    : IPEComm1531.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:25.122218+00:00
-- url     : https://prove2.me/theorems/59f3c73d-cd71-4116-8db5-8f09088fcd0a
-- title:
--   Lemma 3.3 — nonzero $p_x\in V_{|x|+\delta r}$ vanishing where $x$ has ones, computable in polynomial time
-- statement:
--   Let $(V_b)$ be any family satisfying the conclusions of Theorem 3.2, including its polynomial-time basis algorithm. Then there is an assignment $x\mapsto p_x$ such that for every tower length $r$ and every $x\in\{0,1\}^r$
--   $$p_x\in V_{|x|+\delta r}\setminus\{0\},\qquad p_x(i)=0\ \text{ whenever } i\in[r],\ x(i)=1,$$
--   and one deterministic machine computes all $2r$ values of $p_x$ from $x$ in time polynomial in $r$.
--
--   The roots of $p_x$ record the positions of the ones of $x$, which is how an accepting product equality forces two strings to be close.
--
--   Differences from the source:
--   - generalization: the specific objects constructed in Theorem 3.2 → every family satisfying the stated conclusions of Theorem 3.2; reason: the source proof uses only those conclusions; the source objects satisfy them, so the Lean statement specializes to the source
--   - encoding: construction and evaluation of p_x in poly(r) time → one polynomial-time machine outputs the full value table of p_x from (r in unary, x); reason: evaluation at any point is a lookup in the table; the code length is 2r+1
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, Lemma 3.3, p.8 (proof in Appendix C, p.18)

import Mathlib
import Definitions.Def_IPEComm1531_Main_Spaces

namespace IPEComm1531.Main

/-- Lemma 3.3 (prescribed roots), p.8. -/
theorem lemma_3_3 (S : Spaces) (hS : S.Good) (hE : S.Effective) :
    ∃ p : Prescribed, PrescribedCorrect S p ∧ PrescribedEffective p := by sorry

end IPEComm1531.Main
