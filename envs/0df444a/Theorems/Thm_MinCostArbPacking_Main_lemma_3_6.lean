-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_3_6
-- name    : MinCostArbPacking.Main.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:58.459996+00:00
-- url     : https://prove2.me/theorems/068a7610-c5bb-46d4-bd62-e20384144b3b
-- title:
--   Lemma 3.6 — unweighted forest packing in $O(k^2(m_H+n_H)\log(kn_H))$ [AK26]
-- statement:
--   **Lemma 3.6** (Unweighted forest packing; [AK26, Theorem 1.1 and Appendix A.5], cited). Let $H$ be a digraph with $n_H$ vertices and $m_H$ arcs. One computes a maximum-cardinality union of $k$ forests in $H$ with indegree at most $k$ at every vertex, together with a forest decomposition, deterministically in
--
--   $$O\big(k^2(m_H+n_H)\log(kn_H)\big)$$
--
--   time. If every vertex of $H$ has indegree at most $k$, the output is a basis of $\mathcal G^k(H)$.
--
--   Formally: one program and an absolute constant $C$ such that on every digraph with $n_H\ge1$ the output $B$, with its forest labels, is a union of $k$ forests with indegree $\le k$ everywhere and of maximum cardinality among all such subsets, and is a basis of $\mathcal G^k(H)$ when all indegrees of $H$ are at most $k$.
--
--   Differences from the source:
--   - encoding: running time $O(f)$ in the model of §3.1 (exact arithmetic and comparisons in constant time) → one program of the unit-cost real RAM `Machine`, chosen before the input, halting within $C\cdot f$ executed instructions with an absolute constant $C$, for every word bound $W \ge (\mathrm{size}+2)^{c}$; reason: the standard reading of a deterministic time bound; the step count is intrinsic to the interpreter
--   - reading: "a maximum-cardinality union of $k$ forests in $H$ with indegree at most $k$ at every vertex" → maximum among the subsets of $H$ that are unions of $k$ forests and have indegree at most $k$ everywhere, for every $H$; reason: the other reading (indegree $\le k$ as a hypothesis on $H$) would make the lemma's second sentence redundant; this reading implies it
--   - encoding: a digraph $H$ → a digraph with $n_H\ge1$ vertices; reason: excludes the empty instance on which $O(0)$ time is meaningless
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §3.4, p.9, Lemma 3.6 (cited: Arkhipov–Kolmogorov, SODA 2026, Thm 1.1 and App. A.5)

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_IO
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 3.6 (Unweighted forest packing; [AK26, Theorem 1.1 and Appendix A.5]), p.9: for every
digraph `H` with `n_H` vertices and `m_H` arcs, one program computes a maximum-cardinality union of
`k` forests in `H` with indegree at most `k` at every vertex, together with a forest decomposition,
deterministically in `O(k²(m_H + n_H) log(k n_H))` steps (at most `C` times that, `C` absolute); if
every vertex of `H` has indegree at most `k`, the output is a basis of `𝒢^k(H)`. -/
theorem lemma_3_6 : ∃ (P : Machine.Program) (cw : ℕ) (C : ℝ), ∀ H : DigraphInput, 1 ≤ H.k → 1 ≤ H.n →
    ∀ W : ℤ, ((H.size + 2 : ℕ) : ℤ) ^ cw ≤ W →
      Machine.HaltsWithin P W H.inI []
        (C * ((H.k : ℝ) ^ 2 * (H.m + H.n) * logL ((H.k : ℝ) * H.n)))
        (fun o _ => ForestPackingOutput H o) := by sorry

end MinCostArbPacking.Main
