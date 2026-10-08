-- Prove2me | Theorems.Thm_MatroidProphetKW_Single_lemma_1_2
-- name    : MatroidProphetKW.Single.lemma_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:45.480149+00:00
-- url     : https://prove2.me/theorems/770467d3-1bc6-494a-b08c-cb424b98ff3d
-- title:
--   Lemma 1.2 — the exchange bijection does not increase weight, $w'(\phi(v)) \ge w'(v)$
-- statement:
--   Let $\mathcal M = (\mathcal U, \mathcal I)$ be a matroid, $V, R \in \mathcal I$ two **disjoint** independent sets of equal cardinality, and $w' : \mathcal U \to \mathbb R$ a weight function. Suppose $R$ has the maximum weight among all $|R|$-element independent subsets of $V \cup R$. Then every bijection $\phi : V \to R$ with the exchange property of part 1, i.e. $(R - \{\phi(v)\}) \cup \{v\} \in \mathcal I$ for every $v \in V$, satisfies
--   $$w'(\phi(v)) \;\ge\; w'(v) \qquad \text{for every } v \in V.$$
--
--   Combined with part 1, this provides the weight-dominating exchange that bounds the sum in (12).
--
--   **Formalization Note** The page states part 2 without requiring $V$ and $R$ to be disjoint. Without disjointness it is false: for $V = R = \{a, b\}$ independent with $w'(a) = 1$, $w'(b) = 0$, the swap $\phi(a) = b$, $\phi(b) = a$ has the exchange property (the sets $\{a\}$, $\{b\}$ are independent) but $w'(\phi(a)) < w'(a)$. In the paper's only use (the proof of Proposition 2) $V$ is disjoint from $R = R(A)$, and the paper's proof of part 2 treats $(R - \{\phi(v)\}) \cup \{v\}$ as an $|R|$-element set, which needs $v \notin R$. Disjointness is therefore added.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 8, Lemma 1, part 2

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting

namespace MatroidProphetKW.Single

/-- Lemma 1, part 2 (Kleinberg–Weinberg, arXiv:1201.4764v1, p. 8), for disjoint `V`, `R`: if `V`
and `R` are disjoint independent sets with `|V| = |R|`, and `R` has the maximum `w′`-weight among
all `|R|`-element independent subsets of `V ∪ R`, then every bijection `φ : V → R` with the exchange
property of part 1 satisfies `w′(φ(v)) ≥ w′(v)` for all `v ∈ V`. -/
theorem lemma_1_2 {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (V R : Finset α) (hV : M.Indep (↑V : Set α)) (hR : M.Indep (↑R : Set α))
    (hcard : V.card = R.card) (hdisj : Disjoint V R) (w' : α → ℝ)
    (hmax : ∀ S : Finset α, S ⊆ V ∪ R → M.Indep (↑S : Set α) → S.card = R.card →
      wt w' S ≤ wt w' R)
    (φ : V ≃ R) (hφ : ∀ v : V, M.Indep (↑(insert (v : α) (R.erase (φ v : α))) : Set α)) :
    ∀ v : V, w' v ≤ w' (φ v) := by sorry

end MatroidProphetKW.Single
