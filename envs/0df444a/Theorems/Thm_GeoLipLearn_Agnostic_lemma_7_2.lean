-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_lemma_7_2
-- name    : GeoLipLearn.Agnostic.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:52:01.225925+00:00
-- url     : https://prove2.me/theorems/31a0cb2c-c0c0-4a54-a975-79c347cd0628
-- title:
--   Lemma 7.2 (Smoothing a uniformly small residual)
-- statement:
--   Let $L\ge0$, $0<\beta\le1/16$, and let $v:\mathbb R^d\to[-L,L]$ be measurable. Let $h:\mathbb R^d\to\mathbb R$ be globally 1-Lipschitz, and suppose $|v(x)-h(x)|\le\beta$ for every $x$. For $U=U_\beta v$,
--   $$\operatorname{Lip}(U)\le1+\sqrt\beta,\qquad\|U-v\|_2\le\sqrt\beta+2\beta.$$
--   This states the analytic smoothing bound for any such pair; the source pair $v=\widehat R[q]$, $h=R[q]$ is included.
--
--   Differences from the source:
--   - encoding: Euclidean space, Gaussian norms, and the norm of the scalar gradient → EuclideanSpace ℝ (Fin d), stdGaussian, extended nonnegative eLpNorm, and the operator norm of fderiv; reason: the scalar derivative has the same norm as the Euclidean gradient; extended norms retain infinity rather than returning a junk zero
--   - generalization: v=R̂[q] and h⋆=R[q] in the setting of Section 7, with L≥1 → any measurable v bounded by L≥0 and any globally 1-Lipschitz h uniformly β-close to v; reason: every source pair has these properties; the analytic smoothing estimate applies to the larger class without a polynomial or stored-probe hypothesis
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 28, Lemma 7.2

import Definitions.Def_GeoLipLearn_Agnostic_Gaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem lemma_7_2 (d : ℕ) (L β : ℝ) (hL : 0 ≤ L) (hβ : 0 < β ∧ β ≤ 1/16)
    (v h : Space d → ℝ) (hv : Measurable v) (hr : InRange L v)
    (hh : LipschitzWith 1 h) (hclose : ∀ x, |v x-h x| ≤ β) :
    LipschitzWith (1 + NNReal.sqrt (Real.toNNReal β)) (ou β v) ∧
    normG 2 (ou β v - v) ≤ ENNReal.ofReal (Real.sqrt β + 2*β) := by sorry

end GeoLipLearn.Agnostic
