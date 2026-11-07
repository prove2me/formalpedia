-- Prove2me | Theorems.Thm_MinrankTW_eq_14
-- name    : MinrankTW.eq_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:20.447401+00:00
-- url     : https://prove2.me/theorems/240b0817-f975-41ab-9cad-61c766d9185e
-- title:
--   Eq. (14) — the tables count partial assignments by relation and interior rank; $F_{\mathrm{root}}(\{0\},z)=Z(z)$
-- statement:
--   Let $S$ be entry constraints on $m\times n$ matrices over $\mathbb F_q$ and consider a well-formed nice decomposition with the tables $F_t$ of the recursion of Section 3.3.
--
--   1. At every node $t$ and for every linear relation $R$,
--   $$
--   F_t(R,z)=\sum_{M_t:\ R(M_t)=R} z^{\operatorname{rank}M_t[I_t,I_t]},
--   $$
--   the sum ranging over the assignments of the entries introduced in the subtree, each $(M_t)_{ij}\in S_{ij}$, all other entries zero.
--   2. If every $S_{ij}$ is nonempty and $t$ is an empty root at which every support entry has been introduced, then $F_t(\{0\},z)=Z(z)$, the rank enumerator.
--
--   This is the correctness of the dynamic program before the fast join.
--
--   **Formalization Note** $R(M_t)$ is taken with the forgotten rows and columns as interior and the current bag as bag; "every support entry introduced" says that the introduced positions are exactly the $(i,j)$ for which $S_{ij}$ contains a nonzero element.
--
--   Differences from the source:
--   - encoding: bag and interior coordinates of a bag with a columns and c rows (F^a ⊕ F^c) → ambient coordinates in F^n × F^m supported on the bag (interior and bag disjoint); reason: the same relation with the bag coordinates embedded; same instances
--   - encoding: a nice decomposition with empty leaves and root → a tree of operations with a well-formedness predicate; the root conditions (empty bag, every support entry introduced) as hypotheses; reason: the same decompositions
--   - generalization: nice decompositions refined from a tree decomposition of the support graph → every well-formed nice decomposition (for (14)) and every well-formed one with an empty root introducing exactly the support entries (for the root identity); reason: the refined decompositions of p.10 are well formed, so the statement specializes to them
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 3.3, pp.11–12, Eq. (14)

import Mathlib
import Definitions.Def_MinrankTW_rankEnum
import Definitions.Def_MinrankTW_relOfPartial
import Definitions.Def_MinrankTW_interiorRank
import Definitions.Def_MinrankTW_NiceTree
import Definitions.Def_MinrankTW_dpTable

namespace MinrankTW

open Polynomial

open Classical in
/-- **Eq. (14) and the root identity**, Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §3.3, pp.11–12. For entry constraints `S` and
a well-formed nice decomposition, the tables of the recursion satisfy, at every node `t`,
`F_t(R, z) = ∑_{M_t : R(M_t) = R} z^{rank M_t[I_t, I_t]}` (14), the sum ranging over the
assignments of the entries introduced in the subtree, each `(M_t)_ij ∈ S_ij` (all other entries
zero). At an empty root at which every support entry has been introduced (every `S_ij`
nonempty), `F_root({0}, z) = Z(z)`.

**Formalization Note** An assignment of the introduced entries is a matrix that lies in `S_ij`
at the introduced positions and is `0` elsewhere. `R(M_t)` is `relOfPartial` with interior the
forgotten rows/columns and bag the current bag; `{0}` is `⊥`. "Every support entry introduced"
is: the introduced positions are exactly the `(i, j)` with a nonzero element in `S_ij`. -/
theorem eq_14 {F : Type} [Field F] [Fintype F] [DecidableEq F] {m n : ℕ}
    (S : Fin m → Fin n → Finset F) :
    (∀ t : NiceTree m n, t.WF → ∀ R : Submodule F ((Fin n → F) × (Fin m → F)),
      dpTable S t R =
        ∑ M ∈ (Finset.univ : Finset (Matrix (Fin m) (Fin n) F)).filter (fun M =>
            (∀ i j, ((i, j) ∈ t.assigned → M i j ∈ S i j) ∧ ((i, j) ∉ t.assigned → M i j = 0)) ∧
            relOfPartial M t.forgottenRows t.bagRows t.forgottenCols t.bagCols = R),
          X ^ interiorRank M t.forgottenRows t.forgottenCols) ∧
    (∀ t : NiceTree m n, (∀ i j, (S i j).Nonempty) → t.WF → t.bagRows = ∅ → t.bagCols = ∅ →
      (∀ i j, (i, j) ∈ t.assigned ↔ ∃ a ∈ S i j, a ≠ 0) →
      dpTable S t ⊥ = rankEnum S) := by sorry

end MinrankTW
