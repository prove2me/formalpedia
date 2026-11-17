-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_33
-- name    : MonoidProdQ.Supplement.theorem_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:20:37.494369+00:00
-- url     : https://prove2.me/theorems/8f22d1df-20a9-4f78-a810-be93332ffaad
-- title:
--   Theorem 33 — minimum-weight matroid bases with $O(\min\{n,\sqrt{nr}\})$ record queries
-- statement:
--   Let $\mathcal M$ be a known matroid of rank $r$ on a finite ground set $E$, and let $W\subseteq\mathbb R$ be finite. The input consists of $n\ge1$ records $x_i\in(E\times W)\cup\{\bot\}$, one query revealing a whole record. There is a universal constant $C$ such that:
--
--   1. the canonical minimum-weight basis (greedy in increasing order of $(w_i,i)$, as an index set) can be computed with bounded error using at most $C\min\{n,\sqrt{nr}\}$ queries, and so can the selected records together with their indices;
--   2. if $r=0$, the canonical basis is empty on every input and both outputs need no query.
--
--   This recovers, for instance, the minimum spanning forest bound of Dürr, Heiligman, Høyer and Mhalla.
--
--   **Formalization Note** The matroid is a Mathlib matroid whose ground set is all of $E$, and $r$ is its rank. The canonical basis and the record output are the definitions `canonicalBasis` and `selectedRecords`; the promise domain is all record sequences.
--
--   Differences from the source:
--
--   - encoding: a known finite matroid M = (E, I) → a Mathlib matroid on a finite type E with ground set all of E; reason: every finite matroid is one on the type of its ground set
--   - encoding: the greedy algorithm in increasing order of (w_i, i) → its rank-increase characterization: i selected iff x_i nonnull and e_i ∉ cl(elements of earlier nonnull records); reason: the paper states this characterization (p.43); it selects the same indices
--   - encoding: returning the selected records as well as their indices → the vector listing x_i at selected positions and ⊥ elsewhere; reason: determines both
--   - encoding: O(min{n, √(nr)}), universal constant → ∃ C > 0 chosen before the matroid, W and n; reason: the stated universality
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 33 (Minimum-weight matroid bases), p.44

import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_MonoidProdQ_Supplement_canonicalBasis
import Definitions.Def_MonoidProdQ_Supplement_selectedRecords

open scoped ENNReal

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 33 (Minimum-weight matroid bases),
p.44: "Let M be a known finite matroid of rank r, and let W ⊆ ℝ be finite. For n ≥ 1, the
canonical minimum-weight basis of n input records can be computed with bounded error using
O(min{n, √(nr)}) quantum queries. The implicit constant is universal. The same bound permits
returning the selected records as well as their indices. If r = 0, the answer is empty and no
query is needed." Two conjuncts:

1. one universal `C > 0` such that for every finite matroid, weight alphabet and `n ≥ 1`, both
   the canonical basis (as an index set) and the selected records with their indices have
   `Q_{1/3} ≤ C·min{n, √(nr)}`;
2. if `r = 0`, the canonical basis is empty on every input and both outputs have `Q_{1/3} = 0`.

**Formalization Note.** The matroid is a Mathlib `Matroid E` on a finite type `E` with ground set
all of `E`; `r = rk(E)` is `M.eRank.toNat`. An input record is `Option (E × W)` (`none` = `⊥`),
one query revealing a whole record; the promise domain is all of `(E × W ∪ {⊥})ⁿ`. The canonical
basis is `canonicalBasis M W` (greedy in increasing `(wᵢ, i)` order, written through the
rank-increase characterization of p.43), the record output `selectedRecords M W`. -/
theorem theorem_33 :
    (∃ C : ℝ, 0 < C ∧
      ∀ (E : Type u) [Fintype E] [DecidableEq E] (M : Matroid E), M.E = Set.univ →
        ∀ (W : Finset ℝ) (n : ℕ), 1 ≤ n →
          (Q13 (canonicalBasis M W (n := n)) Finset.univ : ℝ≥0∞) ≤
              ENNReal.ofReal (C * min (n : ℝ) (Real.sqrt (n * M.eRank.toNat))) ∧
            (Q13 (selectedRecords M W (n := n)) Finset.univ : ℝ≥0∞) ≤
              ENNReal.ofReal (C * min (n : ℝ) (Real.sqrt (n * M.eRank.toNat)))) ∧
    (∀ (E : Type u) [Fintype E] [DecidableEq E] (M : Matroid E), M.E = Set.univ →
      M.eRank = 0 → ∀ (W : Finset ℝ) (n : ℕ), 1 ≤ n →
        (∀ x : Fin n → Option (E × W), canonicalBasis M W x = ∅) ∧
          Q13 (canonicalBasis M W (n := n)) Finset.univ = 0 ∧
          Q13 (selectedRecords M W (n := n)) Finset.univ = 0) := by sorry

end MonoidProdQ.Supplement
