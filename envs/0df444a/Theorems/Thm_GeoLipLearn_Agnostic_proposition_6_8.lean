-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_proposition_6_8
-- name    : GeoLipLearn.Agnostic.proposition_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:53:09.726833+00:00
-- url     : https://prove2.me/theorems/395d0f82-d43d-4e37-90eb-8b85f0c65b7b
-- title:
--   Proposition 6.8 (Uniform convergence)
-- statement:
--   There is a universal positive natural constant $C$ with the following property. Let $Q$ be a polynomial of degree at most $k$, $q=C_L(Q)$, $L\ge1$, $s>0$, $0<\beta\le\sigma_s\le1/2$ and $0<\delta\le1/2$. If
--   $$N\ge(d+1)^{C(k+L^2/\sigma_s^2)}\beta^{-C}\log(2/\delta),$$
--   then $N$ independent standard Gaussian probes produce, with probability at least $1-\delta$,
--   $$|\widehat R[q](x)-R[q](x)|\le\beta\quad\text{for every }x\in\mathbb R^d.$$
--   All queries use the same probes. This is uniform convergence over the entire query space.
--
--   Differences from the source:
--   - encoding: Euclidean space, Gaussian norms, and the norm of the scalar gradient → EuclideanSpace ℝ (Fin d), stdGaussian, extended nonnegative eLpNorm, and the operator norm of fderiv; reason: the scalar derivative has the same norm as the Euclidean gradient; extended norms retain infinity rather than returning a junk zero
--   - encoding: with probability at least 1 − δ → a measurable subset of the specified product probability space, of measure at least ENNReal.ofReal (1 − δ), on which all conclusions hold; reason: this records an actual measurable success event rather than using outer measure of an arbitrary set
--   - encoding: a universal C and a supremum bounded by β → a universal positive natural C and a bound for every query x; reason: increasing C preserves sufficiency on this domain; boundedness of the supremum is exactly the pointwise uniform inequality
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 25, Proposition 6.8

import Definitions.Def_GeoLipLearn_Agnostic_Corrector

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem proposition_6_8 : ∃ C : ℕ, 0 < C ∧
    ∀ (d k N : ℕ) (L s β δ : ℝ) (Q : Poly d), Q.totalDegree ≤ k →
      1 ≤ L → 0 < s → 0 < β → β ≤ sigma s → sigma s ≤ 1/2 →
      0 < δ → δ ≤ 1/2 →
      (d+1 : ℝ)^((C : ℝ)*(k+L^2/(sigma s)^2))*β^(-(C : ℝ))*Real.log (2/δ) ≤ N →
      HighProbability (Measure.pi fun _ : Fin N => gaussian d) δ (fun z =>
        let q := fun x => clip L (evalPoly Q x)
        ∀ x, |empiricalCorrector L s q z x - corrector L s q x| ≤ β) := by sorry

end GeoLipLearn.Agnostic
