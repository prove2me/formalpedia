-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_tail_biased_weak
-- name    : HypercliqueAC0.FixedDepth.tail_biased_weak
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T00:59:44.26585+00:00
-- url     : https://prove2.me/theorems/8f719cdb-a552-5523-a1c7-0f7dc8d39f34
-- title:
--   $p$-biased Fourier tail of depth-$h$ circuits: weight above $Kw^h$ is at most $4(G+1)2^{-w}$
-- statement:
--   For every integer $h\ge1$ there is a constant $K_h>0$ with the following property. Let $X$ be a finite set, let $0<p<1$, and let $f\colon\{0,1\}^X\to\{0,1\}$ be computed by a depth-$h$ circuit $C$ with $G(C)$ gates. Let $\widehat f_p(S)$ be the $p$-biased Fourier coefficients of $f$ with respect to the product measure $\mu_p$. Then for every integer $w\ge0$ and every real $D\ge K_hw^h$,
--
--   $$\sum_{|S|\ge D}\widehat f_p(S)^2\le 4\,(G(C)+1)\,2^{-w}.$$
--
--   The constant does not depend on $p$. This is the biased analogue of the uniform tail bound, obtained as in the proof of Lemma 3.3 of the source by writing a $\mu_p$-sample as a projection of a uniform one; it controls the Fourier tails of the prefix increments in Lemma 4.3.
-- source:
--   Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/830.pdf, §3.4, Lemma 3.3 and its proof (after Blais–O'Donnell–Wimmer 2008), in the form needed for the range of degrees used in Lemma 4.5.

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

theorem tail_biased_weak (h : ℕ) (hh : 1 ≤ h) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : Type) [Fintype X] (p : ℝ) (C : MantriCVQ.ACCircuit X) (w : ℕ),
      0 < p → p < 1 → C.depth ≤ h → ∀ D : ℝ, K * (w : ℝ) ^ h ≤ D →
        fourierTailGE p (boolReal C.eval) D ≤
          4 * ((C.gates.length : ℝ) + 1) * (2 : ℝ) ^ (-(w : ℝ)) := by sorry

end HypercliqueAC0.FixedDepth
