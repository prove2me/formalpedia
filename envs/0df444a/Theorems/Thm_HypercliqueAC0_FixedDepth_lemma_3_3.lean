-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_3_3
-- name    : HypercliqueAC0.FixedDepth.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T19:12:26.74364+00:00
-- url     : https://prove2.me/theorems/bbdccffd-79eb-4b67-b0a2-0b54ad101a1a
-- title:
--   Lemma 3.3: the p-biased Fourier tail bound
-- statement:
--   Fix an integer $h\ge1$. There exists a real $K>0$ depending only on $h$ such that, for every finite variable set $X$, every $0<p<1$, every Boolean function $f$ computed by a circuit of depth at most $h$ with at most $\sigma\ge2$ gates, and every real $D\ge0$,
--
--   $$\sum_{|S|\ge D}\widehat f_p(S)^2\le4\cdot2^{-D/[K(\log_2\sigma)^{h-1}]}.$$
--
--   The factor four is the printed constant. This supplies the tail estimate for biased random hypergraphs.
--
--   **Formalization Note** The constant $K$ is chosen before $X,p,f,\sigma,C,D$ and need not equal the constant in Theorem 3.2.
--
--   Differences from the source:
--   - encoding: Boolean-cube Fourier coefficients and product-measure probabilities → Boolean functions converted to real indicators and finite weighted sums over all assignments; reason: the finite product distribution and every coefficient have the same values
--   - encoding: $O_h((\log\sigma)^{h-1})$ → a positive constant depending only on $h$, uniform in the bias and all other data; reason: spells out the printed asymptotic notation
--   - encoding: the §3.2 convention that every gate reaches the output → arbitrary circuits, including unused gates and repeated input sources, with gate count equal to the gate-list length; reason: pruning unused gates and deleting repeated sources preserve output and depth and cannot increase gate count
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.12 (PDF p.14), Lemma 3.3

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section

namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- Lemma 3.3, p.12 (PDF 14). K depends only on h, uniformly over p. -/
theorem lemma_3_3 (h : ℕ) (hh : 1 ≤ h) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : Type) [Fintype X] (p : ℝ)
      (f : (X → Bool) → Bool) (σ : ℝ) (C : MantriCVQ.ACCircuit X),
      0 < p → p < 1 → 2 ≤ σ → C.depth ≤ h → (C.gates.length : ℝ) ≤ σ →
      (∀ x, C.eval x = f x) → ∀ D : ℝ, 0 ≤ D →
        fourierTailGE p (boolReal f) D ≤
          4 * (2 : ℝ) ^ (-D / (K * (Real.logb 2 σ) ^ (h - 1))) := by sorry

end HypercliqueAC0.FixedDepth
