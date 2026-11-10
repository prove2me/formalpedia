-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_lemma_8_2
-- name    : GeoLipLearn.Agnostic.lemma_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:52:03.048205+00:00
-- url     : https://prove2.me/theorems/e022dd92-51e1-47e9-991f-27bffc12fc8b
-- title:
--   Lemma 8.2 (Clipping in absolute distance)
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be globally 1-Lipschitz with $\|f\|_1\le3R$ and $R\ge1$. For every $r>0$ and $T\ge6R+r$,
--   $$\|f-C_T(f)\|_1\le\frac2r e^{-r^2/2}.$$
--   All norms are under the standard Gaussian law. This bounds the absolute-distance cost of clipping a Lipschitz comparator.
--
--   Differences from the source:
--   - encoding: Euclidean space, Gaussian norms, and the norm of the scalar gradient → EuclideanSpace ℝ (Fin d), stdGaussian, extended nonnegative eLpNorm, and the operator norm of fderiv; reason: the scalar derivative has the same norm as the Euclidean gradient; extended norms retain infinity rather than returning a junk zero
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 32, Lemma 8.2

import Definitions.Def_GeoLipLearn_Agnostic_Gaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem lemma_8_2 (d : ℕ) (f : Space d → ℝ) (R r T : ℝ)
    (hf : LipschitzWith 1 f) (hR : 1 ≤ R) (hn : normG 1 f ≤ ENNReal.ofReal (3*R))
    (hr : 0 < r) (hT : 6*R+r ≤ T) :
    normG 1 (fun x => f x-clip T (f x)) ≤ ENNReal.ofReal ((2/r)*Real.exp (-r^2/2)) := by sorry

end GeoLipLearn.Agnostic
