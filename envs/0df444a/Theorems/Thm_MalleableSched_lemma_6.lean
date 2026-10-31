-- Prove2me | Theorems.Thm_MalleableSched_lemma_6
-- name    : MalleableSched.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:04.31676+00:00
-- url     : https://prove2.me/theorems/7e6867f3-517c-4ac8-b834-34b9a858d017
-- title:
--   Lemma 6 — $G(x')$ has an orientation with every in-degree at most 1
-- statement:
--   Throughout, as in §2.1: every speed function $g_j$ is nonnegative and fractionally subadditive, $\mathbf S$ is an assignment, $C=L(\mathbf S)$ is finite, and $\Delta\in\mathbb R^{M\times J}$ satisfies both conditions of Lemma 4: $\sum_{i\in S_j}\Delta_{ij}=g_j(S_j)$ and $\sum_{i\in T}\Delta_{ij}\le g_j(T)$ for all $j$ and $T\subseteq S_j$.
--
--   Let $x'$ be an extreme point solution of (LP1) and let $G(x')$ be its support graph on the node set $J\cup M$, with an edge $\{i,j\}$ for every $j\in J$ and $i\in S_j^+$ with $x'_{ij}>0$. Then $G(x')$ has an orientation in which every node has in-degree at most $1$.
--
--   The orientation splits each job's support into at most one in-edge (a candidate single machine $i_j$) and out-edges $\bar S_j$, which the rounding of Lemmas 7–9 uses.
--
--   Differences from the source:
--   - encoding: an orientation of G(x′) in which every node has in-degree at most 1 → toJob : Fin m → Fin n → Prop (edge (i, j) directed i → j iff toJob i j) with InDegLeOne (supportEdges x) toJob; reason: each edge of the bipartite support graph gets one direction; values off the edge set are irrelevant
--   - encoding: C := L(S) → a real C with 0 ≤ C and maxLoad g S = ENNReal.ofReal C; reason: (LP1) needs C to be a real number; this excludes only L(S) = ∞, where Theorem 1 holds for every S′
--   - encoding: decision variables xᵢⱼ only for i ∈ S⁺ⱼ → a full m × n real matrix with xᵢⱼ = 0 for i ∉ S⁺ⱼ; reason: an affine copy of the paper's feasible region; feasible points and extreme points correspond
--   - generalization: processing times fⱼ : 2^M → ℝ≥0 finite on non-empty sets (p.2), i.e. gⱼ(S) > 0 for S ≠ ∅ → only gⱼ(S) ≥ 0; speed 0 gives processing time ∞ in ℝ≥0∞; reason: the paper itself uses fⱼ(∅) = ∞ and infinite processing times (p.3, Appendix A.1); instances with positive speeds are a special case
--   - encoding: fⱼ(S) = 1/gⱼ(S), with 1/0 = ∞; loads and L(S) = max over machines → procTime = (ENNReal.ofReal (g j S))⁻¹ in ℝ≥0∞; maxLoad = ⨆ over machines of the summed times; reason: ℝ≥0∞ has 0⁻¹ = ⊤, matching fⱼ(∅) = ∞; a finite ⨆ is the maximum
--   - encoding: job set J and machine set M; set functions on 2^M → Fin n and Fin m (0-based); Finset (Fin m); reason: Lean convention; any finite sets relabel to these
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Lemma 6, p.8

import Mathlib
import Definitions.Def_MalleableSched_Model
import Definitions.Def_MalleableSched_LP1
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace MalleableSched

open UnrelatedSched.TwoApprox

/-- **Lemma 6 (orientation of the support graph).**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs
under Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, Lemma 6, p.8: "Now consider an extreme point solution x′ to (LP1). … consider the support
graph G(x′) of x′ on the node set J ∪ M, which has an edge {i, j} for every j ∈ J and i ∈ S+_j with
x′_ij > 0. … Lemma 6. The graph G(x′) has an orientation such that any node has an in-degree of at
most 1."

**Formalization Note.** Standing context of §2.1 (p.8): every `g j` is nonnegative and fractionally subadditive, `S` is an
assignment, `C := L(S)` (here a real `C ≥ 0` with `maxLoad g S = ENNReal.ofReal C`), and `Δ`
satisfies both constraints of Lemma 4.
`G(x′)` has edge set `supportEdges x`; for `x` feasible this is the paper's edge set (entries
outside `S⁺ⱼ` are `0`). An orientation is `toJob` (see `InDegLeOne`). -/
theorem lemma_6 {n m : ℕ}
    (g : Fin n → Finset (Fin m) → ℝ) (hg0 : ∀ j S, 0 ≤ g j S)
    (hFS : ∀ j, FractionallySubadditive (g j))
    (S : Fin n → Finset (Fin m)) (hS : IsAssignment S)
    (C : ℝ) (hC : 0 ≤ C) (hL : maxLoad g S = ENNReal.ofReal C)
    (Δ : Matrix (Fin m) (Fin n) ℝ)
    (hΔ1 : ∀ j, ∑ i ∈ S j, Δ i j = g j (S j))
    (hΔ2 : ∀ j, ∀ T ⊆ S j, ∑ i ∈ T, Δ i j ≤ g j T)
    (x : Matrix (Fin m) (Fin n) ℝ) (hx : x ∈ Set.extremePoints ℝ (LP1Region Δ S C)) :
    ∃ toJob : Fin m → Fin n → Prop, InDegLeOne (supportEdges x) toJob := by sorry

end MalleableSched
