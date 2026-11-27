-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_Supplement_lemma_5
-- name    : MLRPCake.EnvyFree.Supplement.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:05:39.570806+00:00
-- url     : https://prove2.me/theorems/0e896a46-3c57-48fb-ab81-90bc13ee83ab
-- title:
--   Lemma 5 — under MLRP every cake division is weakly dominated by an allocation, and Pareto optimal allocations can be put in MLRP order
-- statement:
--   Let $\mathcal C=\langle[n],\{f_i\}_i\rangle$ be a cake-division instance whose value densities satisfy the monotone likelihood ratio property, with the agents indexed in MLRP order ($f_{i+1}/f_i$ nondecreasing on $[0,1]$). Then:
--
--   1. for every cake division $D=\{D_1,\dots,D_n\}$ there is an allocation $J=\{J_1,\dots,J_n\}$ (one interval per agent, assigned in any order) with
--   $$v_i(J_i)\ge v_i(D_i)\qquad\text{for all } i;$$
--   2. for every allocation $I$ that is Pareto optimal over all cake divisions there is an allocation $I'$ with $v_i(I'_i)=v_i(I_i)$ for all $i$ in which the intervals appear left to right in the MLRP order: $I'_i=[x'_{i-1},x'_i]$ with $0=x'_0\le\dots\le x'_n=1$.
--
--   The first part reduces welfare maximization over all cake divisions to allocations; the second lets the welfare algorithms restrict to allocations in MLRP order.
--
--   Differences from the source:
--   - encoding: agents 1,…,n indexed in the MLRP order (p. 7, w.l.o.g.), densities strictly positive on [0,1] → agents 0,…,n−1 (Fin n) with the published IsMLRP (consecutive ratios f_{i+1}/f_i nondecreasing, f_i > 0 on [0,1]); reason: the paper fixes this indexing and positivity once in §2; same instances
--   - encoding: an instance with n agents, [n] = {1,…,n} → hypothesis 1 ≤ n; reason: excludes only the empty instance, which has no cake division or allocation
--   - encoding: an allocation I = {I_1,…,I_n} of pairwise-disjoint intervals covering [0,1], assigned in any order → cut points 0 = x 0 ≤ … ≤ x n = 1 (published IsAllocation) and a permutation σ; agent i receives [x (σ i), x (σ i + 1)]; reason: every allocation lists its intervals left to right; σ records who gets which; empty pieces allowed
--   - encoding: a cake division: each D_i a finite collection of intervals, pairwise disjoint, covering [0,1] → each D i a finite union of closed intervals in [0,1], pairwise intersections of measure zero, union [0,1]; reason: adjacent closed pieces share endpoints, which carry no value (non-atomicity, p. 5); disjointness is up to null sets
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 15, Lemma 5 (proof pp. 15–16)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions

namespace MLRPCake.EnvyFree.Supplement

/-- Lemma 5, p. 15: under MLRP (agents in MLRP order), (1) every cake division is weakly
dominated, agent by agent, by some allocation (contiguous pieces, any assignment order), and
(2) for every Pareto optimal allocation there is an allocation giving every agent the same value
whose pieces are assigned left to right in the MLRP order. -/
theorem lemma_5 {n : ℕ} (f : Fin n → ℝ → ℝ) (hn : 1 ≤ n) (hf : IsInstance f) (hm : IsMLRP f) :
    (∀ D : Fin n → Set ℝ, IsCakeDivision D →
      ∃ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x ∧
        ∀ i, bundleVal f i (D i) ≤ pieceVal f x σ i) ∧
    (∀ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x →
      ParetoOptimal f (pieceVal f x σ) →
      ∃ x' : ℕ → ℝ, IsAllocation (n := n) x' ∧
        ∀ i : Fin n, val f i (x' i.val) (x' (i.val + 1)) = pieceVal f x σ i) := by sorry

end MLRPCake.EnvyFree.Supplement
