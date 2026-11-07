-- Prove2me | Theorems.Thm_MatchVec3_beta_count_ne
-- name    : MatchVec3.beta_count_ne
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:41:30.320777+00:00
-- url     : https://prove2.me/theorems/72fc84ec-35bb-4d6a-b469-74eb869f038e
-- title:
--   Proof of Theorem 5.2: the $\beta$-count separates disjoint hyperedges
-- statement:
--   Assume the two-residue structure on $m=p^aq^b$, and let $(U,V)$ be a matching vector family with off-diagonal residues in $\{\alpha,\beta\}$. Let $A,B\subseteq[K]$ be disjoint sets with $|A|=|B|$ and $\sum_{j\in A}u_j=\sum_{j\in B}u_j$, and let $i\in A$. Then
--
--   $$\#\{j\in B:\langle u_j,v_i\rangle=\beta\}\ne\#\{j\in A:\langle u_j,v_i\rangle=\beta\}.$$
--
--   So the exact number of $\beta$-residues seen from a pivot $v_i$ distinguishes $A$ from every other disjoint hyperedge of its fiber. The right side is the paper's $r_A$, since the term $j=i$ is $0\ne\beta$.
--
--   Differences from the source:
--   - generalization: A, B in a matching inside an L-sum fiber, L > q, pivot i(A) → any disjoint A, B of equal size and equal sum, any i ∈ A; reason: the argument uses only these
--   - generalization: "minimal non-prime-power divisor" and "3-restricted" as hypotheses → ResidueStructure and OffDiagIn, with no minimality; reason: these are all the proof uses, Lemma 2.3 yields them from the page's hypotheses, and they imply 3-restriction; if only one of α, β occurs the statement still holds
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), proof of Theorem 5.2, pp.14–15

import Mathlib
import Definitions.Def_MatchVec3_IsMVFamily
import Definitions.Def_MatchVec3_ResidueStructure
import Definitions.Def_MatchVec3_OffDiagIn

namespace MatchVec3

/-- **The β-count separation** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256 44199413…),
proof of Theorem 5.2, pp.14–15): for disjoint `A, B` with the same size and the same sum, and a pivot
`i ∈ A`, the number of `j ∈ B` with `⟨u_j, v_i⟩ = β` differs from the number of `j ∈ A` with
`⟨u_j, v_i⟩ = β`.

**Formalization Note** `i ∈ A` and `Disjoint A B` force `A ≠ B`. The diagonal term `j = i` is not
counted on the `A` side since `⟨u_i, v_i⟩ = 0 ≠ β`. -/
theorem beta_count_ne {m p q a b n K : ℕ} {α β : ZMod m}
    (hstr : ResidueStructure m p q a b α β)
    (U V : Fin K → Fin n → ZMod m) (hfam : IsMVFamily U V) (hoff : OffDiagIn U V α β)
    (A B : Finset (Fin K)) (hdisj : Disjoint A B) (hcard : A.card = B.card)
    (hsum : ∑ j ∈ A, U j = ∑ j ∈ B, U j) (i : Fin K) (hi : i ∈ A) :
    (B.filter fun j => U j ⬝ᵥ V i = β).card ≠ (A.filter fun j => U j ⬝ᵥ V i = β).card := by sorry

end MatchVec3
