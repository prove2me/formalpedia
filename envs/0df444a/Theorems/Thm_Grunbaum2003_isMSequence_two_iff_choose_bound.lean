-- Prove2me | Theorems.Thm_Grunbaum2003_isMSequence_two_iff_choose_bound
-- name    : Grunbaum2003.isMSequence_two_iff_choose_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T03:41:50.414728+00:00
-- url     : https://prove2.me/theorems/e0bba83c-9cdc-436c-b0c6-4e89f2d79b5f
-- title:
--   Length-two Macaulay sequences are exactly the triangular-number bound
-- statement:
--   For a natural-number sequence $g$, the length-two Macaulay condition is exactly
--
--   $$
--   \operatorname{IsMSequence}(2,g)
--   \quad\Longleftrightarrow\quad
--   g_0=1\ \text{ and }\ g_2\le {g_1+1\choose 2}.
--   $$
--
--   No entries beyond $g_2$ are constrained. In dimensions four and five, this gives the complete numerical input condition in the sufficiency direction of the simplicial $g$-theorem.
--
--   For a positive integer $N$, choose the largest integer $a$ with ${a\choose 2}\le N$. Pascal's identity gives a unique remainder satisfying
--
--   $$
--   N={a\choose 2}+r,\qquad 0\le r<a.
--   $$
--
--   If $r=0$, the two-binomial expansion has one term, and its inverse Macaulay boundary is $a-1$. If $r>0$, the expansion is
--
--   $$
--   N={a\choose 2}+{r\choose 1},
--   $$
--
--   and its boundary is $a$. Thus either expansion has boundary at most $g_1$ precisely when $N\le {g_1+1\choose 2}$. The zero value uses the empty expansion, exactly as in the canonical definition.
--
--   The first Macaulay condition imposes only $g_0=1$: a positive $g_1$ has the one-binomial expansion ${g_1\choose 1}$, with boundary one. Combining these two observations proves both directions.
--
--   This result classifies the admissible numerical sequences. It does not construct a simplicial polytope or prove Billera–Lee realization.
-- source:
--   Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §10.6, pp. 198a–198b (PDF pp. 235–236), inverse Macaulay boundary definition; this lemma explicitly evaluates that definition in length two.

import Definitions.Def_Grunbaum2003_IsMSequence
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

namespace Grunbaum2003

theorem isMSequence_two_iff_choose_bound (g : ℕ → ℕ) :
    IsMSequence 2 g ↔ g 0 = 1 ∧ g 2 ≤ Nat.choose (g 1 + 1) 2 := by sorry

end Grunbaum2003
