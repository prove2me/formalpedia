-- Prove2me | Theorems.Thm_MatroidProphetKW_Single_lemma_1_1
-- name    : MatroidProphetKW.Single.lemma_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:08.448129+00:00
-- url     : https://prove2.me/theorems/1aac1e7d-6eb5-4c49-9ae2-d1738d3fc6cb
-- title:
--   Lemma 1.1 — bijective exchange between independent sets of equal size
-- statement:
--   Let $\mathcal M = (\mathcal U, \mathcal I)$ be a matroid and $V, R \in \mathcal I$ two independent sets of equal cardinality. Then there is a bijection $\phi : V \to R$ such that
--   $$(R - \{\phi(v)\}) \cup \{v\} \in \mathcal I \qquad \text{for every } v \in V.$$
--
--   This is Corollary 39.12a of Schrijver's *Combinatorial Optimization*; it is used, in the contraction $\mathcal M/A$, to bound the marginal losses $w'(R(A)) - w'(R(A \cup \{x\}))$ in (12).
--
--   **Formalization Note** The matroid is Mathlib's `Matroid α` on a finite type, with any ground set; $\phi$ is an equivalence between the subtypes of $V$ and $R$.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 8, Lemma 1, part 1 (Schrijver, Combinatorial Optimization, Corollary 39.12a)

import Mathlib

namespace MatroidProphetKW.Single

/-- Lemma 1, part 1 (Kleinberg–Weinberg, arXiv:1201.4764v1, p. 8; Schrijver, Corollary 39.12a):
if `V` and `R` are independent sets of a matroid with `|V| = |R|`, there is a bijection
`φ : V → R` such that `(R − {φ(v)}) ∪ {v}` is independent for every `v ∈ V`. -/
theorem lemma_1_1 {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (V R : Finset α) (hV : M.Indep (↑V : Set α)) (hR : M.Indep (↑R : Set α))
    (hcard : V.card = R.card) :
    ∃ φ : V ≃ R, ∀ v : V, M.Indep (↑(insert (v : α) (R.erase (φ v : α))) : Set α) := by sorry

end MatroidProphetKW.Single
