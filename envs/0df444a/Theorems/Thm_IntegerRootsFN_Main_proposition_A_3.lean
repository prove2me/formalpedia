-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_proposition_A_3
-- name    : IntegerRootsFN.Main.proposition_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:53.40076+00:00
-- url     : https://prove2.me/theorems/be36a635-165b-4acc-a61c-62166f603859
-- title:
--   Proposition A.3 — actual search coverage, cardinality, size and time
-- statement:
--   Let $n,b\ge1$ and $f\in\mathbb Z[x]$ have exact degree $n$ and coefficient magnitudes less than $2^b$. Put $d=\min(n,b)$ and form its top-coefficient truncation $g$. Let $C'$ be the actual finite output of the scale search of p.13, starting with center zero and scale $2^b$, using Test on radius $h+2$, halving the scale and splitting kept centers, and ending with the neighboring integers at scale one. Then all four conclusions hold:
--
--   $$\forall r\in\mathbb Z:\ f(r)=0\ \land\ |r|\ge2\ \Longrightarrow\ r\in C',\qquad |C'|\le21d,$$
--   $$\sum_{c\in C'}\lceil\log_2(2+|c|)\rceil\le21\bigl(5d+b+\tfrac12\log_2(d+1)\bigr),$$
--
--   and one uniform deterministic machine writes this exact distinct list in $\widetilde O(d^3b^2)$ bit steps. Hidden logarithms involve only $d,b$, with machine, constant and exponents fixed before inputs. The search receives the already formed $g$; its output is defined recursively from the coefficient test rather than chosen for its coverage properties.
--
--   This retains coverage, the exact count and total-length constants, and the runtime for the specified search. There is no Pan operation in its definition.
--
--   Differences from the source:
--   - encoding: the search uses the already formed g and returns a set → a deterministic machine on dense g,d,b emits the repetition-free list defined by b halvings and final scale-one tests; reason: list length and summed point size equal the corresponding set quantities; input formation belongs to the main nb cost
--   - encoding: uniform soft-O bit-operation bounds → one finite deterministic multitape machine and positive global C with fixed natural exponents k,l before all varying inputs, bounded by CF(1+log₂(n+1))^k(1+log₂(b+1))^l; reason: shifted logarithms cover the small inputs without changing the allowed polynomial or logarithmic scope; finite initially blank work tapes prohibit advice or assigned costs
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 13, Proposition A.3

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ElementarySearch

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem proposition_A_3 :
    ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
    ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      (∀ r : ℤ, f.IsRoot r → 2 ≤ |r| → r ∈ searchCandidates f n b) ∧
      (searchCandidates f n b).length ≤ 21 * min n b ∧
      (pointSize (searchCandidates f n b) : ℝ) ≤
        21 * (5 * (min n b : ℕ) + (b : ℝ) + (1 : ℝ) / 2 * logTwo ((min n b : ℕ) + 1)) ∧
      Runs M (polynomialWord (truncate f n b) (min n b) b)
        (integersWord (searchCandidates f n b))
        (softBound C k l (min n b) b ((min n b : ℕ) ^ 3 * (b : ℝ) ^ 2)) := by sorry

end IntegerRootsFN.Main
