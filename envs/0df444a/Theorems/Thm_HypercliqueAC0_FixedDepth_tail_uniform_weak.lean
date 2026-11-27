-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_tail_uniform_weak
-- name    : HypercliqueAC0.FixedDepth.tail_uniform_weak
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T00:59:33.042923+00:00
-- url     : https://prove2.me/theorems/b7163e2e-d756-43fb-a6b2-9f205969da91
-- title:
--   Uniform Fourier tail of depth-$h$ circuits: weight above $Kw^h$ is at most $2(G+1)2^{-w}$
-- statement:
--   For every integer $h\ge1$ there is a constant $K_h>0$ with the following property. Let $X$ be a finite set, and let $f\colon\{0,1\}^X\to\{0,1\}$ be computed by a depth-$h$ circuit $C$ with $G(C)$ gates. Then for every integer $w\ge0$ and every real $D\ge K_hw^h$,
--
--   $$\sum_{|S|\ge D}\widehat f(S)^2\le 2\,(G(C)+1)\,2^{-w}.$$
--
--   With $w$ of order $\lambda+\log\sigma$ for circuits with $\sigma$ gates, this gives the Fourier weight bound $2^{-\lambda}$ above degree $O_h((\log\sigma)^{h-1}\lambda)$ whenever $\lambda=O(\log\sigma)$, which is the range of Theorem 3.2 used in the proof of Lemma 4.5 of the source.
--
--   **Formalization Note** The uniform Fourier coefficients are the $p$-biased coefficients of the mission's Fourier interface at $p=1/2$.
-- source:
--   Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/830.pdf, §3.4, Theorem 3.2 (citing Tal, Tight bounds on the Fourier spectrum of AC0, CCC 2017, Theorem 18), in the form needed for the range of degrees used in Lemma 4.5; standard consequence of Håstad's switching lemma and Linial–Mansour–Nisan (J. ACM 1993).

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

theorem tail_uniform_weak (h : ℕ) (hh : 1 ≤ h) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : Type) [Fintype X] (C : MantriCVQ.ACCircuit X) (w : ℕ),
      C.depth ≤ h → ∀ D : ℝ, K * (w : ℝ) ^ h ≤ D →
        fourierTailGE (1 / 2) (boolReal C.eval) D ≤
          2 * ((C.gates.length : ℝ) + 1) * (2 : ℝ) ^ (-(w : ℝ)) := by sorry

end HypercliqueAC0.FixedDepth
