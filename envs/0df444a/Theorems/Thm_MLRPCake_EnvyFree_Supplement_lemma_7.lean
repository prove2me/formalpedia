-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_Supplement_lemma_7
-- name    : MLRPCake.EnvyFree.Supplement.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:09:41.9963+00:00
-- url     : https://prove2.me/theorems/1093d54b-51c4-44ab-b3fb-2b5455084920
-- title:
--   Lemma 7 — some social-welfare maximizing allocation has all its cut points in P
-- statement:
--   Let $\mathcal C$ be a cake-division instance whose value densities satisfy MLRP, agents in MLRP order, and let $P=\{p_{ij}: 1\le i<j\le n\}\cup\{0,1\}$ be the set of switching points together with the endpoints of the cake. Then there is an allocation $S$ with cut points $0=s_0\le s_1\le\dots\le s_n=1$ that maximizes social welfare over all allocations,
--   $$\mathrm{SW}(S)\ge\mathrm{SW}(I)\quad\text{for every allocation } I,$$
--   and all of whose cut points belong to $P$.
--
--   This reduces social-welfare maximization to a grid of $O(n^2)$ points, on which a dynamic program operates (Theorem 3).
--
--   Differences from the source:
--   - encoding: agents 1,…,n indexed in the MLRP order (p. 7, w.l.o.g.), densities strictly positive on [0,1] → agents 0,…,n−1 (Fin n) with the published IsMLRP (consecutive ratios f_{i+1}/f_i nondecreasing, f_i > 0 on [0,1]); reason: the paper fixes this indexing and positivity once in §2; same instances
--   - encoding: an instance with n agents, [n] = {1,…,n} → hypothesis 1 ≤ n; reason: excludes only the empty instance, which has no cake division or allocation
--   - encoding: an allocation I = {I_1,…,I_n} of pairwise-disjoint intervals covering [0,1], assigned in any order → cut points 0 = x 0 ≤ … ≤ x n = 1 (published IsAllocation) and a permutation σ; agent i receives [x (σ i), x (σ i + 1)]; reason: every allocation lists its intervals left to right; σ records who gets which; empty pieces allowed
--   - encoding: a social welfare maximizing allocation → an allocation whose SW is at least that of every allocation (any assignment order); reason: states attainment of the maximum without a real supremum
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 19, Lemma 7

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions
import Definitions.Def_MLRPCake_EnvyFree_Supplement_SwitchPoints

namespace MLRPCake.EnvyFree.Supplement

/-- Lemma 7, p. 19: under MLRP there is a social-welfare maximizing allocation (maximizing over
all allocations, in any assignment order) all of whose cut points lie in the set `P` of
switching points together with `0` and `1`. -/
theorem lemma_7 {n : ℕ} (f : Fin n → ℝ → ℝ) (hn : 1 ≤ n) (hf : IsInstance f) (hm : IsMLRP f) :
    ∃ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x ∧
      (∀ (x' : ℕ → ℝ) (σ' : Equiv.Perm (Fin n)), IsAllocation (n := n) x' →
        SW f x' σ' ≤ SW f x σ) ∧
      ∀ k ≤ n, x k ∈ switchSet f := by sorry

end MLRPCake.EnvyFree.Supplement
