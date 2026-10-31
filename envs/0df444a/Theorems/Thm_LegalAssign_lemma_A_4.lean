-- Prove2me | Theorems.Thm_LegalAssign_lemma_A_4
-- name    : LegalAssign.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:18.961995+00:00
-- url     : https://prove2.me/theorems/00a4ed1d-cbef-4ab7-8653-4dd2c09903ad
-- title:
--   Lemma A.4 — two marriages that do not block each other
-- statement:
--   Let $(G,<)$ be an instance of stable marriage, that is, all quotas equal $1$, and let $M,M'\in\mathcal M(G,\mathbf 1)$. Call an edge $ab\in M\cup M'$ **irregular** if both $a$ and $b$ strictly prefer $M$ to $M'$ or both strictly prefer $M'$ to $M$, an unmatched vertex preferring any partner to none. If $M$ does not block $M'$ and $M'$ does not block $M$, then:
--
--   1. there are no irregular edges;
--   2. $G[M\triangle M']$ is a disjoint union of singletons and cycles;
--   3. a node is matched in $M$ if and only if it is matched in $M'$.
--
--   The lemma extends the opposition-of-interest property of stable matchings to pairs of matchings that merely do not block each other.
--
--   **Formalization Note** Part 2 is stated as "every vertex has degree $0$ or $2$ in $M\triangle M'$".
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - encoding: G[M△M′] is a disjoint union of singletons and cycles → every student and every school has degree 0 or 2 in symmDiff M M′; reason: for a finite simple graph the two are the same condition
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Lemma A.4, p.26

import Mathlib
import Definitions.Def_LegalAssign_Instance

namespace LegalAssign

/-- Lemma A.4 (arXiv:1809.08506v2, p.26). In a stable marriage instance (all quotas one), let `M, M'`
be assignments that do not block each other. Then (1) no edge of `M ∪ M'` is irregular, that is, has
both endpoints strictly preferring `M` to `M'` or both strictly preferring `M'` to `M`; (2) every
vertex has degree `0` or `2` in `M △ M'`; (3) a vertex is matched in `M` iff it is matched in `M'`.

**Formalization Note** Part 2 of the source reads "`G[M△M']` is a disjoint union of singletons and
cycles". For a finite simple graph this is exactly "every vertex has degree `0` or `2`", and that is
what is stated. -/
theorem lemma_A_4 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) (hq : ∀ b, G.q b = 1)
    (M M' : Finset (A × B)) (hM : M ∈ G.assignments) (hM' : M' ∈ G.assignments)
    (h : ¬ G.Blocks M M') (h' : ¬ G.Blocks M' M) :
    (∀ a b, (a, b) ∈ M ∪ M' →
      ¬ ((G.StudentStrictlyPrefers M M' a ∧ G.SchoolStrictlyPrefers M M' b) ∨
        (G.StudentStrictlyPrefers M' M a ∧ G.SchoolStrictlyPrefers M' M b))) ∧
    ((∀ a, (studentPartners (symmDiff M M') a).card = 0 ∨
        (studentPartners (symmDiff M M') a).card = 2) ∧
      (∀ b, (schoolPartners (symmDiff M M') b).card = 0 ∨
        (schoolPartners (symmDiff M M') b).card = 2)) ∧
    ((∀ a, (studentPartners M a).Nonempty ↔ (studentPartners M' a).Nonempty) ∧
      (∀ b, (schoolPartners M b).Nonempty ↔ (schoolPartners M' b).Nonempty)) := by sorry

end LegalAssign
