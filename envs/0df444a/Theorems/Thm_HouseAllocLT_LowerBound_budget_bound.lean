-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_budget_bound
-- name    : HouseAllocLT.LowerBound.budget_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:30.560798+00:00
-- url     : https://prove2.me/theorems/4ea3ec53-91e8-4a77-a14b-d1b607400e65
-- title:
--   Theorem 3.1, proof, first display — budget upper bound
-- statement:
--   For $n\ge2$, use the harmonic cutoff quantities $t_n,J_n,B_n$ of (6). Every real vector $x_1,\ldots,x_n$ with $0\le x_j\le1/(n-j+1)$ and $\sum_jx_j\le1$ satisfies
--
--   $$\sum_{j=1}^n(n-j+1)x_j\le B_n.$$
--
--   This is the objective bound in the first displayed calculation of Theorem 3.1's proof. It makes no assumption that the vector is implemented by a mechanism.
--
--   Differences from the source:
--   - encoding: agents, objects and ranks numbered from one → Fin indices numbered from zero; reason: the bijection sends each code index j to the source index j+1
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Theorem 3.1, proof, first display, PDF p. 9 (printed p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_prefixList

open scoped BigOperators ENNReal Topology
open Filter

namespace HouseAllocLT.LowerBound

/-- Theorem 3.1, proof, first display, PDF p.9 (printed p.7).
Every real vector satisfying (3) has objective at most B_n. -/
theorem budget_bound {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1 / ((n - j.val : ℕ) : ℝ))
    (hsum : (∑ j, x j) ≤ 1) :
    (∑ j, ((n - j.val : ℕ) : ℝ) * x j) ≤ B n := by sorry

end HouseAllocLT.LowerBound
