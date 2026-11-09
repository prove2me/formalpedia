-- Prove2me | Theorems.Thm_HSElemKernel_packing_eq_1
-- name    : HSElemKernel.packing_eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:34.304427+00:00
-- url     : https://prove2.me/theorems/b964cb12-790a-48ac-a683-e9ed1bf0c78e
-- title:
--   Section 2.2 and Eq. (1) — a maximal packing gives $|X| \le d|P|$ and $|A \cap W| \le d-1$
-- statement:
--   Let $(U, \mathcal S, k)$ be an instance of $d$-Hitting Set and $P \subseteq \mathcal S$ an inclusion-maximal **packing**: its sets are pairwise disjoint, and no family of pairwise disjoint input sets strictly contains $P$. Put
--   $$X = \bigcup_{A \in P} A, \qquad W = U \setminus X .$$
--   Then
--
--   1. if $|P| > k$, the instance is a NO-instance;
--   2. $|X| \le d\,|P|$;
--   3. if $\emptyset \notin \mathcal S$, every input set intersects $X$;
--   4. if $\emptyset \notin \mathcal S$, then
--   $$|A \cap W| \le d - 1 \quad\text{for every } A \in \mathcal S. \tag{1}$$
--
--   The set $X$ is represented directly by variables in the encoding, while (1) guarantees that each input set needs at most $d - 1$ hashed elements, which keeps the clause width at most $d$.
--
--   Differences from the source:
--   - generalization: the packing built greedily → every inclusion-maximal packing P ⊆ S; reason: the page uses only maximality; the greedy packing is one
--   - reading: "every input set intersects X" and (1), stated after Section 2.1 → clauses 3 and 4 under the hypothesis ∅ ∉ S; reason: Section 2.1 assumes ∅ ∉ S from there on; the empty set meets nothing
--   - encoding: A ∩ W with W = U \ X → A \ X; reason: same set
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 2.2, pp.3–4, Eq. (1) on p.4

import Mathlib
import Definitions.Def_HSElemKernel_IsDHS
import Definitions.Def_HSElemKernel_IsYes

namespace HSElemKernel

/-- **Section 2.2, maximal packing and Eq. (1)** (Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 2.2, pp.3–4): let `P ⊆ S` be an
inclusion-maximal packing (a family of pairwise disjoint input sets not contained in a larger
one) of a `d`-Hitting Set instance, `X = ⋃_{A ∈ P} A` and `W = U \ X`. Then
1. if `|P| > k`, the instance is a NO-instance;
2. `|X| ≤ d|P|`;
3. if `∅ ∉ S`, every input set intersects `X`;
4. if `∅ ∉ S`, `|A ∩ W| ≤ d − 1` for every `A ∈ S` (Eq. (1)).

**Formalization Note** `A ∩ W` is `A \ X`. Clauses 3–4 assume `∅ ∉ S`, the standing
assumption of Section 2.1 under which the page states them: the empty set meets nothing. -/
theorem packing_eq_1 (d : ℕ) (I : HSInstance) (hI : IsDHS d I) (P : Finset (Finset (Fin I.n)))
    (hPS : P ⊆ I.S) (hdisj : (P : Set (Finset (Fin I.n))).PairwiseDisjoint id)
    (hmax : ∀ P' : Finset (Finset (Fin I.n)), P ⊆ P' → P' ⊆ I.S →
      (P' : Set (Finset (Fin I.n))).PairwiseDisjoint id → P' = P) :
    (I.k < P.card → ¬ IsYes I) ∧ (P.biUnion id).card ≤ d * P.card ∧
      (∅ ∉ I.S → ∀ A ∈ I.S, (A ∩ P.biUnion id).Nonempty) ∧
      (∅ ∉ I.S → ∀ A ∈ I.S, (A \ P.biUnion id).card ≤ d - 1) := by sorry

end HSElemKernel
