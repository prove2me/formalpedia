-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_lemma_6_4
-- name    : GeoLipLearn.Agnostic.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:52:56.779337+00:00
-- url     : https://prove2.me/theorems/d68602c9-940b-4d6d-9a3d-f29962431720
-- title:
--   Lemma 6.4 (Corrector computes the Gaussian median)
-- statement:
--   Fix $L>0$ and $s>0$, and let $v:\mathbb R^d\to[-L,L]$ be globally 1-Lipschitz. Let $m_v(x)$ be the lower median of $v(\rho_sx+\sigma_sz)$ for $z\sim\gamma_d$. Then
--   $$R[v](x)=m_v(x)\quad\text{for every }x\in\mathbb R^d.$$
--   The lower median is the infimum of all thresholds with vote probability at least one half. This identifies the corrector on Lipschitz inputs.
--
--   Differences from the source:
--   - encoding: Euclidean space, Gaussian norms, and the norm of the scalar gradient → EuclideanSpace ℝ (Fin d), stdGaussian, extended nonnegative eLpNorm, and the operator norm of fderiv; reason: the scalar derivative has the same norm as the Euclidean gradient; extended norms retain infinity rather than returning a junk zero
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 21, Lemma 6.4

import Definitions.Def_GeoLipLearn_Agnostic_Corrector

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem lemma_6_4 (d : ℕ) (L s : ℝ) (hL : 0 < L) (hs : 0 < s)
    (v : Space d → ℝ) (hv : LipschitzWith 1 v) (hvr : InRange L v) :
    ∀ x, corrector L s v x = lowerMedian s v x := by sorry

end GeoLipLearn.Agnostic
