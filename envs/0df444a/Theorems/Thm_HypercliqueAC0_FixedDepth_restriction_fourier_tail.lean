-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_restriction_fourier_tail
-- name    : HypercliqueAC0.FixedDepth.restriction_fourier_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T00:59:51.93805+00:00
-- url     : https://prove2.me/theorems/152d6af2-e3f8-5a1a-a821-86c4e59ca20a
-- title:
--   Fourier tail via random restrictions: $\sum_{|S|\ge D}\widehat f(S)^2\le 2\Pr_\rho[\mathrm{DT}(f|_\rho)>w]$
-- statement:
--   Let $X$ be a finite set, let $f\colon\{0,1\}^X\to\{0,1\}$, and let $\widehat f(S)$ denote its uniform Fourier coefficients. Let $0<q\le1$, let $w\ge0$ be an integer, and let $D$ be a real number with $4(w+1)\le qD$. Then
--
--   $$\sum_{|S|\ge D}\widehat f(S)^2\le 2\Pr_{\rho\sim\mathcal R_q}\bigl[\mathrm{DT}(f|_\rho)>w\bigr],$$
--
--   where $\mathcal R_q$ is the $q$-random restriction (each coordinate free with probability $q$, otherwise fixed to a uniform bit).
--
--   This is the standard bridge between random restrictions and Fourier concentration: the Fourier weight of $f$ above degree $D$ is controlled by the probability that a random restriction fails to make $f$ a shallow decision tree. It reduces Fourier tail bounds for constant-depth circuits to switching lemmas.
-- source:
--   Linial, Mansour, Nisan, Constant depth circuits, Fourier transform, and learnability, J. ACM 40 (1993), Lemma 7 and §4; see also O'Donnell, Analysis of Boolean Functions (2014), Proposition 3.21 and §4.5; used in the proof of [Tal17, Theorem 18] cited as Theorem 3.2 of Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/830.pdf.

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting
import Definitions.Def_HypercliqueAC0_FixedDepth_Switching

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

theorem restriction_fourier_tail {X : Type} [Fintype X] (q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (f : (X → Bool) → Bool) (w : ℕ) (D : ℝ)
    (hD : 4 * ((w : ℝ) + 1) ≤ q * D) :
    fourierTailGE (1 / 2) (boolReal f) D ≤
      2 * restrictionProb q (fun ρ => ¬ DTDepthLE w (restrictFn ρ f)) := by sorry

end HypercliqueAC0.FixedDepth
