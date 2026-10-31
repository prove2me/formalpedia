-- Prove2me | Theorems.Thm_LegalAssign_lemma_A_5
-- name    : LegalAssign.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:11.143058+00:00
-- url     : https://prove2.me/theorems/33e57d07-57f8-4e89-9dff-014637485e80
-- title:
--   Lemma A.5 — two assignments that do not block each other
-- statement:
--   Let $(G(A\cup B,E),<,q)$ be an instance of the stable assignment problem, let $M,M'\in\mathcal M(G,q)$ be such that $M$ does not block $M'$ and $M'$ does not block $M$, and fix $a\in A$ matched in $M$. Then $a$ is matched in $M'$. Moreover, with $b=M(a)$ and $\bar b=M'(a)$, if $b>_a\bar b$, then there is $\bar a\in M(\bar b)$ with
--   $$a>_{\bar b}\bar a\qquad\text{and}\qquad \bar b>_{\bar a}M'(\bar a).$$
--   Here $M'(\bar a)$ may be empty, and then the last inequality holds by convention.
--
--   This is the one-to-many form of Lemma A.4 used in the proof of Lemma A.6.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Lemma A.5, pp.26–27

import Mathlib
import Definitions.Def_LegalAssign_Instance

namespace LegalAssign

/-- Lemma A.5 (arXiv:1809.08506v2, pp.26–27). Let `M, M'` be assignments that do not block each other
and let `a` be matched in `M`. Then `a` is matched in `M'`; and if `b = M(a)`, `b̄ = M'(a)` and
`b >_a b̄`, there is `ā ∈ M(b̄)` with `a >_b̄ ā` and `b̄ >_ā M'(ā)`. -/
theorem lemma_A_5 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (M M' : Finset (A × B)) (hM : M ∈ G.assignments) (hM' : M' ∈ G.assignments)
    (h : ¬ G.Blocks M M') (h' : ¬ G.Blocks M' M) (a : A)
    (ha : (studentPartners M a).Nonempty) :
    (studentPartners M' a).Nonempty ∧
      ∀ b b', (a, b) ∈ M → (a, b') ∈ M' → G.prefA a b b' →
        ∃ a' ∈ schoolPartners M b', G.prefB b' a a' ∧ G.PrefersToPartner M' a' b' := by sorry

end LegalAssign
