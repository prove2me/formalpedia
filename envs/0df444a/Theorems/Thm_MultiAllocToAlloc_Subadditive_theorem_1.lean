-- Prove2me | Theorems.Thm_MultiAllocToAlloc_Subadditive_theorem_1
-- name    : MultiAllocToAlloc.Subadditive.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:10:06.847901+00:00
-- url     : https://prove2.me/theorems/f8205b62-201d-4662-8ffd-ab411c6f5bc6
-- title:
--   Theorem 1 — a d-multi-allocation (d ≥ 2 a power of 2) yields an allocation A′ ⊆ A with v_i(A′_i) ≥ v_i(A_i)/d − ((d−1)/d)·δ_i
-- statement:
--   Let $d\ge2$ be a power of $2$ ($d=2^k$ with $k\ge1$). There are $n$ agents and a finite set of $m$ items. Every agent $i$ has a valuation $v_i$ on sets of items that is normalized ($v_i(\emptyset)=0$), monotone ($v_i(S)\le v_i(T)$ for $S\subseteq T$) and subadditive ($v_i(S\cup T)\le v_i(S)+v_i(T)$). Let $A=A_1,\dots,A_n$ be a $d$-multi-allocation: bundles of items, possibly intersecting, such that every item belongs to at most $d$ of them. Let $\delta_i=\max_{e\in A_i} v_i(\{e\})$ (and $\delta_i=0$ when $A_i=\emptyset$). Then there is an allocation $A'=A'_1,\dots,A'_n$, that is, pairwise disjoint bundles, with $A'_i\subseteq A_i$ for every $i$ (the paper considers only such allocations, p. 1), such that for every agent $i$
--   $$v_i(A'_i)\ \ge\ \frac{v_i(A_i)}{d}\ -\ \frac{d-1}{d}\,\delta_i .$$
--
--   Differences from the source:
--   - encoding: d ≥ 2 a perfect power of 2 → d : ℕ with ∃ k, 1 ≤ k ∧ d = 2 ^ k, cast to ℝ in the bound; reason: the same set of d
--   - encoding: δ_i = max_{e ∈ A_i} v_i(e) → maxItemValue (v i) (A i), which is the maximum of v_i({e}) over e ∈ A_i when A_i ≠ ∅ and 0 when A_i = ∅; reason: the maximum over an empty bundle is undefined in the paper; with δ_i = 0 and A'_i ⊆ A_i = ∅ the bound reads 0 ≥ 0; any nonnegative convention also makes the empty-bundle inequality true, and no instance with A_i ≠ ∅ changes
-- source:
--   Feige, arXiv:2506.21493v1, Theorem 1, p. 2

import Mathlib
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation

namespace MultiAllocToAlloc.Subadditive

/-- Feige, arXiv:2506.21493v1, Theorem 1, p. 2: let `d ≥ 2` be a power of `2` and `A` a
`d`-multi-allocation of the items `Fin m` to the agents `Fin n`, where every agent has a
normalized monotone subadditive valuation `v_i` and `δ_i = max_{e ∈ A_i} v_i({e})`. Then there
is an allocation `A'` with `A'_i ⊆ A_i` and `v_i(A'_i) ≥ v_i(A_i)/d − ((d − 1)/d)·δ_i` for every
agent `i`. -/
theorem theorem_1 {n m : ℕ} (d : ℕ) (hd : ∃ k : ℕ, 1 ≤ k ∧ d = 2 ^ k)
    (A : Fin n → Finset (Fin m)) (hA : IsMultiAllocation d A)
    (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i)) :
    ∃ A' : Fin n → Finset (Fin m), IsAllocation A' ∧ (∀ i, A' i ⊆ A i) ∧
      ∀ i : Fin n,
        v i (A i) / (d : ℝ) - ((d : ℝ) - 1) / (d : ℝ) * maxItemValue (v i) (A i) ≤
          v i (A' i) := by sorry

end MultiAllocToAlloc.Subadditive
