-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_3_13
-- name    : GlobalUpdatesFO.Upper.lemma_3_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:21:13.954121+00:00
-- url     : https://prove2.me/theorems/20db31da-416c-4509-997e-961aef2f7d19
-- title:
--   Lemma 3.13 — k copies suffice: a disjoint union of t ≥ k structures of one sentence k-type is ≡_k to the union of the first k
-- statement:
--   Let $t \ge k \ge 1$ and let $A_1,\dots,A_t$ be $\Sigma$-structures with the same full sentence $k$-type. Then
--   $$A_1 \uplus \dots \uplus A_t \;\equiv_k\; A_1 \uplus \dots \uplus A_k .$$
--
--   This is the counting threshold of the $k$-pebble game: beyond $k$ copies, further copies of a component are invisible to $\mathrm{FO}^k$. It bounds the size of the type catalogue and is used in the construction of closures.
--
--   Differences from the source:
--   - encoding: A_1 ⊎ … ⊎ A_t over pairwise disjoint universes, all nullary predicates evaluating the same way → Structure.disjointUnion on the sigma type Σ i, V i; a nullary relation holds iff it holds in some summand; reason: every disjoint union is isomorphic to one of this form; the summands agree on nullary relations here because they have the same sentence type and nullary atoms are FO^k sentences
--   - encoding: A_1, …, A_t and the first k of them → A : (i : Fin t) → Structure σ (V i) and the restriction along Fin.castLE (k ≤ t); reason: 0-based indexing
--   - encoding: formulas of FO^k[Σ] with r free variables x̄, up to renaming of bound variables → named-variable Formula over ℕ; IsFOk σ k r φ: WF, free variables among x_0, …, x_{r−1}, and |vars(φ) ∪ {0, …, r−1}| ≤ k; reason: the paper's definition (p. 17) with the free tuple fixed to x_0, …, x_{r−1}; renaming bound variables changes no type
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 24, Lemma 3.13

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula

namespace GlobalUpdatesFO.Upper

theorem lemma_3_13 (σ : Signature) (t k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t)
    (V : Fin t → Type) [∀ i, Fintype (V i)] (A : (i : Fin t) → Structure σ (V i))
    (hA : ∀ i j : Fin t, tp0 k (A i) = tp0 k (A j)) :
    tp0 k (Structure.disjointUnion A) =
      tp0 k (Structure.disjointUnion (fun i : Fin k => A (Fin.castLE hkt i))) := by sorry

end GlobalUpdatesFO.Upper
