-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_merge_arbitrary_subsets
-- name    : MSTCuts2027.Parallel.merge_arbitrary_subsets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:26.280522+00:00
-- url     : https://prove2.me/theorems/56a67622-cd39-4094-9dc0-9d4f1b564506
-- title:
--   Theorem 2 — merging arbitrary subsets (corrected: subset need not be proper)
-- statement:
--   There is a constant $c$ such that for every symmetric real cut function $F$: let $V_1,V_2$ be disjoint vertex sets, listed in the machine's array, let the pointer array hold mincut covers $C_1,C_2$ for all pairs of $V_1$ and of $V_2$, and let $T_1,T_2$ be MSTs of $G_1[V_1],G_1[V_2]$. The proxy program halts with work at most $c\,|V_1|\,|V_2|$ and reports a set $P\subseteq V_1\times V_2$ with
--   $$|P|=\min(|V_1|,|V_2|)$$
--   such that:
--
--   1. for any choice of a mincut for each pair of $P$, these cuts with $C_1\cup C_2$ contain a mincut for every pair of $V_1\times V_2$;
--   2. the graph with edges $T_1\cup T_2\cup P$ has a maximum spanning tree, and every such tree is an MST of $G_1[V_1\cup V_2]$.
--
--   This is the backbone of the framework: arbitrary subsets merge with only $\min(|V_1|,|V_2|)$ new mincut computations.
--
--   Differences from the source:
--   - correction: P ⊊ V₁ × V₂ → P ⊆ V₁ × V₂; reason: with V₁ = {u}, V₂ = {v}, an edge of capacity 1, F({u}) = F({v}) = 1, singleton MSTs and empty covers, the cardinality forces P = V₁ × V₂, contradicting strictness
--   - encoding: V₁, V₂ any disjoint subsets → V₁, V₂ nonempty, because MSTs of G₁[V₁] and G₁[V₂] are required; reason: a tree is nonempty; with an empty set the printed statement is empty as well
--   - encoding: O(·) time bound → explicit constant c fixed before the instance, bounding the work (and depth where stated) of a machine run; reason: the paper gives no numerical constant; c may depend only on the fixed program
--   - encoding: any set of vertices → a duplicate-free list L in the array ord at positions l, …; reason: every finite set has such a listing, so no instance is lost; the list gives the machine random access to the set
--   - encoding: a mincut cover → the cuts that the pointer array M points to, stored as Boolean arrays in the cut store, with the mincut values in real cells; reason: Appendix E stores C and M this way; a cover can always be laid out so
--   - reading: an MST on edges (T₁ ∪ T₂ ∪ P) is an MST for G₁[V₁ ∪ V₂] → such a tree exists, and every such tree is an MST of G₁[V₁ ∪ V₂]; reason: the phrase presupposes existence; the stronger reading is taken
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Theorem 2, printed p. 3, PDF p. 5

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms

namespace MSTCuts2027.Parallel

/-- Theorem 2, corrected (`P ⊆ V₁ × V₂`): the program reports `P` in `O(|V₁||V₂|)` work, `P` has
`min(|V₁|, |V₂|)` pairs, mincuts of `P` together with the two stored covers cover all `V₁ × V₂`
pairs, and any maximum spanning tree on `T₁ ∪ T₂ ∪ P` (one exists) is one of `G₁[V₁ ∪ V₂]`. -/
theorem merge_arbitrary_subsets :
    ∃ c : ℕ, ∀ (n : ℕ) (F : Finset (Fin n) → ℝ), IsSymmetricCutFunction F →
      ∀ (Q : Oracle ℝ n) (σ : Store ℝ) (l₁ l₂ : ℕ) (L₁ L₂ : List (Fin n))
        (T₁ : SimpleGraph {y // y ∈ L₁.toFinset}) (T₂ : SimpleGraph {y // y ∈ L₂.toFinset}),
        IsReady n σ → OrdOK σ l₁ L₁ → OrdOK σ l₂ L₂ → Disjoint L₁.toFinset L₂.toFinset →
        TableOK F σ L₁.toFinset → TableOK F σ L₂.toFinset →
        IsMSTOn F L₁.toFinset T₁ → IsMSTOn F L₂.toFinset T₂ →
        ∃ o : Outcome ℝ,
          Halts (machine Q) algorithms Prog.pProxySet
            [(l₁ : ℤ), (L₁.length : ℤ), (l₂ : ℤ), (L₂.length : ℤ)] σ o ∧
          o.work ≤ c * (L₁.length * L₂.length) ∧
          let P := reportedProxySet o.store.mem L₁ l₁ L₂ l₂
          P ⊆ L₁.toFinset ×ˢ L₂.toFinset ∧
          P.card = min L₁.toFinset.card L₂.toFinset.card ∧
          (∀ C : Fin n × Fin n → Finset (Fin n), (∀ q ∈ P, IsMincut F q.1 q.2 (C q)) →
            ∀ x ∈ L₁.toFinset, ∀ y ∈ L₂.toFinset,
              ∃ D ∈ storedCover σ L₁.toFinset ∪ storedCover σ L₂.toFinset ∪
                  ((P.image C : Finset (Finset (Fin n))) : Set (Finset (Fin n))),
                IsMincut F x y D) ∧
          (∃ T, FlowsNetworks.MultiTerminal.IsMaximalSpanningSubtree (mergeGraph T₁ T₂ P) T
              (capacityOn F (L₁.toFinset ∪ L₂.toFinset))) ∧
          (∀ T, FlowsNetworks.MultiTerminal.IsMaximalSpanningSubtree (mergeGraph T₁ T₂ P) T
              (capacityOn F (L₁.toFinset ∪ L₂.toFinset)) →
            IsMSTOn F (L₁.toFinset ∪ L₂.toFinset) T) := by sorry

end MSTCuts2027.Parallel
