-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_lemma_6_6
-- name    : GeoLipLearn.Agnostic.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:52:52.986195+00:00
-- url     : https://prove2.me/theorems/de34699c-556d-4bf4-83f8-9003887dd548
-- title:
--   Lemma 6.6 (Stability under changes on a small set)
-- statement:
--   For $L>0$, $s>0$ and measurable $v_1,v_2:\mathbb R^d\to[-L,L]$,
--   $$\|R[v_1]-R[v_2]\|_1\le K\Pr_{x\sim\gamma_d}[v_1(x)\ne v_2(x)],\qquad K=c_s\sqrt{2\pi}e^{2L^2/c_s^2},\quad c_s=\sigma_s/\rho_s.$$
--   This is stability of the corrector under changes on a small Gaussian set.
--
--   Differences from the source:
--   - encoding: Euclidean space, Gaussian norms, and the norm of the scalar gradient → EuclideanSpace ℝ (Fin d), stdGaussian, extended nonnegative eLpNorm, and the operator norm of fderiv; reason: the scalar derivative has the same norm as the Euclidean gradient; extended norms retain infinity rather than returning a junk zero
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 22, Lemma 6.6

import Definitions.Def_GeoLipLearn_Agnostic_Corrector

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem lemma_6_6 (d : ℕ) (L s : ℝ) (hL : 0 < L) (hs : 0 < s)
    (v₁ v₂ : Space d → ℝ) (hv₁ : Measurable v₁) (hv₂ : Measurable v₂)
    (hr₁ : InRange L v₁) (hr₂ : InRange L v₂) :
    normG 1 (corrector L s v₁ - corrector L s v₂) ≤
      ENNReal.ofReal (stabilityConstant L s * (gaussian d).real {x | v₁ x ≠ v₂ x}) := by sorry

end GeoLipLearn.Agnostic
