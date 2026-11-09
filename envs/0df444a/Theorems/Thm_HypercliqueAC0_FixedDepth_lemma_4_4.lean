-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_4_4
-- name    : HypercliqueAC0.FixedDepth.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T19:12:36.575733+00:00
-- url     : https://prove2.me/theorems/fbd111e3-ea06-4d16-8fac-c3f0854a853a
-- title:
--   Lemma 4.4: comparing a pair of complete hypergraphs
-- statement:
--   Let $r\ge2$ and $s\ge r$ be integers. Let $0<\Lambda\le1$ and $0<p<1$ satisfy
--
--   $$\binom{s-1}{r-1}\ln(1/p)\le\ln(1/\Lambda).$$
--
--   For any two finite sets $P_1,P_2$ with $|P_1|,|P_2|\le s<|P_1\cup P_2|$,
--
--   $$\Lambda^{|P_1\cup P_2|}p^{-|E(K_{P_1}\cup K_{P_2})|}\le\Lambda^sp^{-\binom sr}.$$
--
--   This is the combinatorial inequality used for the pair terms in the union bound.
--
--   **Formalization Note** Sets may belong to any carrier type; only their finite subsets and equality are used. The edge count is the cardinality of the union of their two families of $r$-element subsets, so common edges are counted once.
--
--   Differences from the source:
--   - encoding: $|E(K_{P_1}\cup K_{P_2})|$ → the cardinality of the union of the two $r$-subset families; reason: this is exactly the edge set in the source; no ambient finite universe is required
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.16 (PDF p.18), Lemma 4.4

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section

namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- Lemma 4.4, p.16 (PDF 18), for finite subsets of any carrier. -/
theorem lemma_4_4 (r s : ℕ) (hr : 2 ≤ r) (hs : r ≤ s)
    (Λ p : ℝ) (hΛ : 0 < Λ) (hΛ1 : Λ ≤ 1) (hp : 0 < p) (hp1 : p < 1)
    (hlog : (Nat.choose (s - 1) (r - 1) : ℝ) * Real.log (1 / p) ≤ Real.log (1 / Λ))
    {V : Type*} (P₁ P₂ : Finset V)
    (hP₁ : P₁.card ≤ s) (hP₂ : P₂.card ≤ s) (hunion : s < (P₁ ∪ P₂).card) :
    Λ ^ (P₁ ∪ P₂).card * p ^ (-((P₁.powersetCard r ∪ P₂.powersetCard r).card : ℝ)) ≤
      Λ ^ s * p ^ (-(Nat.choose s r : ℝ)) := by sorry

end HypercliqueAC0.FixedDepth
