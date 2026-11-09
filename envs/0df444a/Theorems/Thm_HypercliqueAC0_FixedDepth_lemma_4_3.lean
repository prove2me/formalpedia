-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_4_3
-- name    : HypercliqueAC0.FixedDepth.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T19:12:26.834057+00:00
-- url     : https://prove2.me/theorems/ed3754e7-cccf-48da-b547-7b1a715f1262
-- title:
--   Lemma 4.3: spanning probability through prefix increments
-- statement:
--   Let $H_0$ be a fixed $r$-uniform hypergraph on $v$ labeled vertices, including isolated vertices, where $1\le v<m$. Let $H$ be its image under a uniform injection into $[m]$, independently of $G\sim\mu_p$ with $0<p<1$. Let $f_0,\ldots,f_t$ be the prefixes of an AND or OR gate with arbitrary Boolean input functions, and put $d_i=f_i-f_{i-1}$. For every integer $D\ge v$,
--
--   $$\Pr[\exists i\in[t]:f_i\text{ spans }H]\le p^{-|E(H_0)|}\left[\left(\frac{eD}{m}\right)^v+(|E(H_0)|+1)^v\sum_{i=1}^t\sum_{|S|>D}\widehat d_{i,p}(S)^2\right].$$
--
--   Here $e=\exp(1)$. This target connects spanning with Fourier tails of the real prefix increments. There is no circuit hypothesis or lower bound on $r$.
--
--   **Formalization Note** Positive prefix indices use the interval from one through the input-list length. The random injection is averaged uniformly and independently of the hypergraph. Every one of the $v$ labeled vertices is retained.
--
--   Differences from the source:
--   - encoding: $[m]=\{1,\ldots,m\}$ and $r$-subsets → $\mathrm{Fin}\,m$ with edge subtype of cardinality $r$; reason: a relabeling bijection preserves the entire hypergraph and all circuit instances
--   - encoding: Boolean-cube Fourier coefficients and product-measure probabilities → Boolean functions converted to real indicators and finite weighted sums over all assignments; reason: the finite product distribution and every coefficient have the same values
--   - encoding: a uniform injection independent of $G$ → the reciprocal injection count times a sum over injections of the product-weight event probability; reason: the injection type is nonempty because $v<m$ and the finite product is the same independent distribution
--   - encoding: monomials of the restricted real multilinear polynomial → nonzero Möbius coefficients on the exact subtype of missing edges; reason: the verified expansion identifies these coefficients with the source polynomial
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.14 (PDF p.16), Lemma 4.3

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section

namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- Lemma 4.3, p.14 (PDF 16). All v vertices of H₀ are retained. -/
theorem lemma_4_3 (m r v : ℕ) (hv : 1 ≤ v) (hvm : v < m)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (H₀ : Finset (Edge v r))
    (isAnd : Bool) (inputs : List ((Edge m r → Bool) → Bool))
    (D : ℕ) (hD : v ≤ D) :
    prefixSpanningProbability p H₀ isAnd inputs ≤
      p ^ (-(H₀.card : ℝ)) *
        ((Real.exp 1 * (D : ℝ) / (m : ℝ)) ^ v +
          ((H₀.card : ℝ) + 1) ^ v *
            ∑ i ∈ Finset.Icc 1 inputs.length,
              fourierTailGT p (prefixIncrement isAnd inputs i) D) := by sorry

end HypercliqueAC0.FixedDepth
