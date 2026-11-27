-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_Supplement_theorem_2
-- name    : MLRPCake.EnvyFree.Supplement.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:06:13.71184+00:00
-- url     : https://prove2.me/theorems/aba88710-b411-4c46-8605-cf41b315212e
-- title:
--   Theorem 2 — under MLRP every envy-free allocation is Pareto optimal over all cake divisions
-- statement:
--   Let $\mathcal C$ be a cake-division instance whose value densities satisfy the monotone likelihood ratio property. If $I=\{I_1,\dots,I_n\}$ is an allocation (one interval per agent, assigned in any order) that is envy-free,
--   $$v_i(I_i)\ge v_i(I_j)\qquad\text{for all agents } i,j,$$
--   then $I$ is Pareto optimal over the set of all cake divisions: no division $D$, in which agents may receive finitely many intervals, has $v_i(D_i)\ge v_i(I_i)$ for all $i$ with strict inequality for some agent.
--
--   This extends Weller's theorem in the MLRP setting: fairness and efficiency are achieved together by contiguous pieces, so the allocation computed for Theorem 1 is also Pareto optimal up to the precision of the computation.
--
--   Differences from the source:
--   - encoding: agents 1,…,n indexed in the MLRP order (p. 7, w.l.o.g.), densities strictly positive on [0,1] → agents 0,…,n−1 (Fin n) with the published IsMLRP (consecutive ratios f_{i+1}/f_i nondecreasing, f_i > 0 on [0,1]); reason: the paper fixes this indexing and positivity once in §2; same instances
--   - encoding: an instance with n agents, [n] = {1,…,n} → hypothesis 1 ≤ n; reason: excludes only the empty instance, which has no cake division or allocation
--   - encoding: an allocation I = {I_1,…,I_n} of pairwise-disjoint intervals covering [0,1], assigned in any order → cut points 0 = x 0 ≤ … ≤ x n = 1 (published IsAllocation) and a permutation σ; agent i receives [x (σ i), x (σ i + 1)]; reason: every allocation lists its intervals left to right; σ records who gets which; empty pieces allowed
--   - encoding: a cake division: each D_i a finite collection of intervals, pairwise disjoint, covering [0,1] → each D i a finite union of closed intervals in [0,1], pairwise intersections of measure zero, union [0,1]; reason: adjacent closed pieces share endpoints, which carry no value (non-atomicity, p. 5); disjointness is up to null sets
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 9, Theorem 2 (restated and proved p. 17, §6.1)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions

namespace MLRPCake.EnvyFree.Supplement

/-- Theorem 2, p. 9: under MLRP every envy-free allocation (contiguous pieces, any assignment
order) is Pareto optimal over the set of all cake divisions. -/
theorem theorem_2 {n : ℕ} (f : Fin n → ℝ → ℝ) (hn : 1 ≤ n) (hf : IsInstance f) (hm : IsMLRP f)
    (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)) (hx : IsAllocation (n := n) x)
    (hef : IsEnvyFree f x σ) :
    ParetoOptimal f (pieceVal f x σ) := by sorry

end MLRPCake.EnvyFree.Supplement
