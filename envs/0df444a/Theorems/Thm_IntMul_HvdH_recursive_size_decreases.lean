-- Prove2me | Theorems.Thm_IntMul_HvdH_recursive_size_decreases
-- name    : IntMul.HvdH.recursive_size_decreases
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T14:34:45.70677+00:00
-- url     : https://prove2.me/theorems/bd6dd2f2-ecb5-4c98-b264-b911c093551e
-- title:
--   Proposition 5.4 — positivity and decrease of the recursive input
-- statement:
--   Let $d\ge2$ and let $n,b,p,T,r$ satisfy the parameter constraints of Proposition 5.4. The recursive multiplication input length is positive and strictly smaller than the original input length:
--
--   $$1\le 3rp<n.$$
--
--   This arithmetic lemma supplies the decreasing size needed for recursive implementations and ensures that a machine's positive-size correctness theorem applies to each recursive call. It asserts no machine construction or running-time estimate.
-- source:
--   Supporting formalization of Harvey and van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021), 563–617, DOI 10.4007/annals.2021.193.2.4; author preprint https://www.texmacs.org/joris/nlogn/nlogn.pdf, Proposition 5.4, printed pages 40–41. The clocked formulation is an explicit operational strengthening needed for the reduction, not a separately numbered theorem of the source.

import Definitions.Def_IntMul_HvdH_StepParameters
import Mathlib.Tactic

open IntMul.HvdH

theorem IntMul.HvdH.recursive_size_decreases (d n b p T r : ℕ) (hd : 2 ≤ d)
    (h : StepParameters d n b p T r) : 1 ≤ 3 * r * p ∧ 3 * r * p < n := by sorry
