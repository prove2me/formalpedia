-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_Supplement_lemma_8_1
-- name    : HypercliqueAC0.FixedDepth.Supplement.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:28:30.044766+00:00
-- url     : https://prove2.me/theorems/84dce50c-fa8e-48a1-bb50-3df43c647741
-- title:
--   Lemma 8.1: fixing all of two-list OV except one vector leaves at least $\sum_{s\le\min(n_2,M_d)}\binom{M_d}{s}$ subfunctions
-- statement:
--   Let $d\ge2$ and put
--   $$M_d=\binom{d}{\lfloor d/2\rfloor}.$$
--   Let $n_1,n_2\ge1$ be integers, and consider two-list Orthogonal Vectors on a first list of $n_1$ vectors and a second list of $n_2$ vectors from $\{0,1\}^d$: it outputs one exactly when some vector of the first list and some vector of the second list have no coordinate where both are one. Fix any vector $i$ of the first list. As the variables outside vector $i$ range over all assignments, the resulting functions of vector $i$ take at least
--   $$\sum_{s=0}^{\min\{n_2,M_d\}}\binom{M_d}{s}$$
--   distinct values, i.e. there are at least that many distinct subfunctions on vector $i$.
--
--   This count is the input to Nechiporuk's formula lower bound in the proof of the depth-three wire bound for $2\text{-}\mathsf{OV}$.
--
--   **Formalization Note** The count is the cardinality of the set of distinct functions $\{0,1\}^d\to\{0,1\}$, not the number of assignments. $\lfloor d/2\rfloor$ is natural-number division.
--
--   Differences from the source:
--   - encoding: two lists of vectors from $\{0,1\}^d$ → Boolean variables indexed by $(\mathrm{Fin}\,n_1\times\mathrm{Fin}\,d)\sqcup(\mathrm{Fin}\,n_2\times\mathrm{Fin}\,d)$; reason: a relabeling bijection preserves every instance
--   - encoding: "distinct functions of this vector" after fixing the other variables → the cardinality of the image of all full assignments under the map sending an assignment to the function of vector $i$ with the other variables taken from it; reason: the assignment's own values on vector $i$ are overwritten, so the image is exactly the set of subfunctions
--   - reading: "outside one vector of the first list" → for every vector $i$ of the first list; reason: the universal reading is the stronger one, and the two readings are equivalent because permuting the first list preserves the function
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.24 (PDF p.26), Lemma 8.1

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Supplement_TwoListOV

noncomputable section

namespace HypercliqueAC0.FixedDepth.Supplement
open scoped BigOperators

/-- Lemma 8.1, p. 24 (PDF 26). `M_d = C(d, ⌊d/2⌋)` (`d / 2` is natural division). For every
vector `i` of the first list, the number of distinct functions of that vector obtained by fixing
all other variables of two-list `2-OV` is at least `∑_{s=0}^{min(n₂, M_d)} C(M_d, s)`. -/
theorem lemma_8_1 (d : ℕ) (hd : 2 ≤ d) (n₁ n₂ : ℕ) (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (i : Fin n₁) :
    ∑ s ∈ Finset.range (min n₂ (Nat.choose d (d / 2)) + 1), Nat.choose (Nat.choose d (d / 2)) s ≤
      (subfunctionsOnFirstVector (twoListOV n₁ n₂ d) i).card := by sorry

end HypercliqueAC0.FixedDepth.Supplement
