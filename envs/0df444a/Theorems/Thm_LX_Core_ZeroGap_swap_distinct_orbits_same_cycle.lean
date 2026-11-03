-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_swap_distinct_orbits_same_cycle
-- name    : LX.Core.ZeroGap.swap_distinct_orbits_same_cycle
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:20:54.046509+00:00
-- url     : https://prove2.me/theorems/e202bd4a-6fe3-42f1-bbfc-aa58a05ab47e
-- title:
--   A transposition between distinct orbits merges its two endpoints into one cycle
-- statement:
--   A transposition between distinct orbits merges its two endpoints into one cycle.
--
--   Let $n$ be a natural number and let $I_n=\{0,\ldots,n-1\}$; this set may be empty. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N) (p : \mathfrak S(I_n)) (a b : I_{n}), \neg \operatorname{Cyc} p a b \to  (\operatorname{swap} a b\, p)_{\rm cycle} a b
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/SwapOrbitMerge.lean#L7-L46

/-
Adapted from https://github.com/snow-ghost/glushkov-lx-lean at 8cddcd222b591673dc63475d9d45b9ed5c6eb92c.
MIT License

Copyright (c) 2026 S. Uskov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib
import Definitions.Def_LX_Graph

namespace LX.Core
end LX.Core
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ}

theorem LX.Core.ZeroGap.swap_distinct_orbits_same_cycle (p : State n) (a b : Fin n)
    (hnot : ¬p.SameCycle a b) : (Equiv.swap a b*p).SameCycle a b := by sorry
