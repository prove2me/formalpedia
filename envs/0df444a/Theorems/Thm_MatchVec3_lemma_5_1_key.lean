-- Prove2me | Theorems.Thm_MatchVec3_lemma_5_1_key
-- name    : MatchVec3.lemma_5_1_key
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:41:29.966274+00:00
-- url     : https://prove2.me/theorems/862bc3a2-863f-4dbd-a11c-78e4fdacdb6f
-- title:
--   Proof of Lemma 5.1: two sets in a $q$-sum fiber are disjoint with one cross residue
-- statement:
--   Assume the two-residue structure on $m=p^aq^b$, and let $(U,V)$ be a matching vector family with off-diagonal residues in $\{\alpha,\beta\}$. If $A\ne B$ are $q$-subsets of $[K]$ with $\sum_{i\in A}u_i=\sum_{j\in B}u_j$, then $A$ and $B$ are disjoint, and
--
--   $$\langle u_j,v_i\rangle=\alpha\qquad\text{for all }i\in A,\ j\in B.$$
--
--   This is the mechanism of the base case: representatives of the sets of a $q$-sum fiber form a 2-restricted family modulo $q^b$.
--
--   Differences from the source:
--   - generalization: cross inner products have "only one value α modulo q^b" → equality ⟨u_j, v_i⟩ = α in Z_m; reason: the equality implies the congruence, and the page's count argument gives it
--   - generalization: "minimal non-prime-power divisor" and "3-restricted" as hypotheses → ResidueStructure and OffDiagIn, with no minimality; reason: these are all the proof uses, Lemma 2.3 yields them from the page's hypotheses, and they imply 3-restriction; if only one of α, β occurs the statement still holds
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), proof of Lemma 5.1, p.13

import Mathlib
import Definitions.Def_MatchVec3_IsMVFamily
import Definitions.Def_MatchVec3_ResidueStructure
import Definitions.Def_MatchVec3_OffDiagIn

namespace MatchVec3

/-- **Key point of the proof of Lemma 5.1** (Aggarwal, Obremski, STOC 2027 submission (manuscript
sha256 44199413…), proof of Lemma 5.1, p.13): two distinct sets `A, B` in the same `q`-sum fiber are
disjoint, and their cross inner products `⟨u_j, v_i⟩` (`i ∈ A`, `j ∈ B`) have one value `α`.

**Formalization Note** The page says "one value α modulo q^b". The equality here is in `Z_m`, which
implies it. `i` and `j` range over `A` and `B` in this order; the statement also applies to the
pair `B, A`. -/
theorem lemma_5_1_key {m p q a b n K : ℕ} {α β : ZMod m}
    (hstr : ResidueStructure m p q a b α β)
    (U V : Fin K → Fin n → ZMod m) (hfam : IsMVFamily U V) (hoff : OffDiagIn U V α β)
    (A B : Finset (Fin K)) (hA : A.card = q) (hB : B.card = q) (hAB : A ≠ B)
    (hsum : ∑ i ∈ A, U i = ∑ j ∈ B, U j) :
    Disjoint A B ∧ ∀ i ∈ A, ∀ j ∈ B, U j ⬝ᵥ V i = α := by sorry

end MatchVec3
