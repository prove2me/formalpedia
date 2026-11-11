-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_lemma_3_5
-- name    : IntegerRootsFN.Main.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:58.980212+00:00
-- url     : https://prove2.me/theorems/fa0433e2-2ea7-4eb8-ba3c-3b0bfcfbbe5c
-- title:
--   Lemma 3.5 — exact evaluation charged by total point size
-- statement:
--   Fix any natural cardinality multiplier $K$. There is one deterministic machine with positive time constant and fixed natural logarithmic exponents, depending only on $K$. For all $n,b\ge1$, let $f\in\mathbb Z[x]$ have exact degree $n$ and coefficient magnitudes strictly less than $2^b$, and let $c_1,\ldots,c_m\in\mathbb Z$ be any list with $m\le Kn$. Put $S=\sum_i\lceil\log_2(2+|c_i|)\rceil$. The machine computes the entire exact ordered value list with
--
--   $$T\le\widetilde O(nb+nS).$$
--
--   The list may be empty or contain repeated points. Input coefficients, points and output values are signed binary data. The hidden logarithms depend only on $n,b$, not on $S$, point magnitudes or resulting values. Constants are fixed before all polynomials and point lists.
--
--   This is the literal scope stated by the p.2 convention. The proof on p.11 explicitly absorbs $\log S$, which is a source scope discrepancy still requiring proof work; no additional $S=O(b)$ promise or polylogarithmic $S$ factor is introduced.
--
--   Differences from the source:
--   - encoding: integers n,b≥1 and coefficients given in binary → positive natural parameters, dense signed fixed-width coefficients, finite signed binary outputs; reason: this represents every source input; signs, delimiters, input reads and output writes count as machine steps
--   - encoding: m=O(n) → for every fixed K, m≤Kn with uniform machine and constants depending only on K; reason: this makes the fixed cardinality multiplier explicit and still covers arbitrary integer point lists
--   - encoding: uniform soft-O bit-operation bounds → one finite deterministic multitape machine and positive global C with fixed natural exponents k,l before all varying inputs, bounded by CF(1+log₂(n+1))^k(1+log₂(b+1))^l; reason: shifted logarithms cover the small inputs without changing the allowed polynomial or logarithmic scope; finite initially blank work tapes prohibit advice or assigned costs
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 10, Lemma 3.5; proof p.11

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary

set_option autoImplicit false

namespace IntegerRootsFN.Main

/-- Literal n,b-only logarithmic scope; the proof's log S absorption is disclosed. -/
theorem lemma_3_5 :
    ∀ K : ℕ, ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
    ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
    ∀ cs : List ℤ, cs.length ≤ K * n →
      Runs M (evaluationWord f n b cs) (integersWord (cs.map f.eval))
        (softBound C k l n b ((n : ℝ) * b + n * (pointSize cs : ℝ))) := by sorry

end IntegerRootsFN.Main
