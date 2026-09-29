-- Prove2me | Theorems.Thm_GrothendieckTeichmuller_mzv_stuffle
-- name    : GrothendieckTeichmuller.mzv_stuffle
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T21:49:55.533093+00:00
-- url     : https://prove2.me/theorems/c4d4dd11-0f58-4d43-9455-3703f415c7b2
-- title:
--   Proposition 6.1 — the stuffle relations for multiple zeta values
-- statement:
--   Call a word $u = n_1\cdots n_k$ of natural numbers **admissible** when all its letters are at least $1$ and, if it is non-empty, $n_1 \ge 2$; exactly then does the series defining $\zeta(u)$ converge. Let $u \ \text{⧢}\ v$ denote the stuffle (quasi-shuffle) product, the multiset of words produced by the recursion
--
--   $$n w \ \text{⧢}\ n' w' = n\,(w \ \text{⧢}\ n' w') + n'\,(n w \ \text{⧢}\ w') + (n+n')\,(w \ \text{⧢}\ w') .$$
--
--   Then for all admissible $u$ and $v$,
--
--   $$\zeta(u)\,\zeta(v) \;=\; \sum_{w \in u \,\text{⧢}\, v} \zeta(w),$$
--
--   the sum being over the multiset $u \ \text{⧢}\ v$, with multiplicities. For example $\zeta(2,3)\zeta(5) = \zeta(5,2,3)+\zeta(2,5,3)+\zeta(2,3,5)+\zeta(7,3)+\zeta(2,8)$.
--
--   These are the **stuffle relations**, one of the two families of relations whose common refinement forms the double shuffle relations; they come from multiplying the defining nested sums and splitting according to the order of the summation indices.
-- source:
--   Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 6.1, p. 53 (definition of multiple zeta values, stuffle product, Proposition 6.1, shuffle product, Proposition 6.2, Euler's identity zeta(2,1) = zeta(3))

import Definitions.Def_GT_multizeta

namespace GrothendieckTeichmuller

theorem mzv_stuffle (u v : List ℕ) (hu : IsAdmissible u) (hv : IsAdmissible v) :
    mzv u * mzv v = ((stuffle u v).map mzv).sum := by sorry

end GrothendieckTeichmuller
