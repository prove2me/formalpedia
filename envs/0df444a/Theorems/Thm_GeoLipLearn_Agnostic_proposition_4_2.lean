-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_proposition_4_2
-- name    : GeoLipLearn.Agnostic.proposition_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:52:03.974523+00:00
-- url     : https://prove2.me/theorems/e70771a4-40c3-4d8c-911f-8a7a76237ff3
-- title:
--   Proposition 4.2 (Uniform convergence of squared defect)
-- statement:
--   Let $A\ge1$, $0<\beta,\delta\le1/2$, and let $z_1,\ldots,z_N$ be independent standard Gaussian vectors in $\mathbb R^d$. If
--   $$N\ge\left(\frac{A(d+1)^k}{\beta\delta}\right)^{10},$$
--   then with probability at least $1-\delta$, simultaneously for every degree-at-most-$k$ polynomial $p$ with $\|p\|_2^2\le A$,
--   $$\left|\frac1N\sum_i(\|\nabla p(z_i)\|-1)_+^2-\Gamma(p)\right|\le\beta.$$
--   This is uniform convergence for the population defect constraint.
--
--   Differences from the source:
--   - encoding: Euclidean space, Gaussian norms, and the norm of the scalar gradient → EuclideanSpace ℝ (Fin d), stdGaussian, extended nonnegative eLpNorm, and the operator norm of fderiv; reason: the scalar derivative has the same norm as the Euclidean gradient; extended norms retain infinity rather than returning a junk zero
--   - encoding: with probability at least 1 − δ → a measurable subset of the specified product probability space, of measure at least ENNReal.ofReal (1 − δ), on which all conclusions hold; reason: this records an actual measurable success event rather than using outer measure of an arbitrary set
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 16, Proposition 4.2

import Definitions.Def_GeoLipLearn_Agnostic_Gaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem proposition_4_2 (d k N : ℕ) (A β δ : ℝ) (hA : 1 ≤ A)
    (hβ : 0 < β ∧ β ≤ 1/2) (hδ : 0 < δ ∧ δ ≤ 1/2)
    (hN : (A*(d+1 : ℝ)^k/(β*δ))^10 ≤ (N : ℝ)) :
    HighProbability (Measure.pi fun _ : Fin N => gaussian d) δ (fun z =>
      ∀ p : Poly d, p.totalDegree ≤ k → normG 2 (evalPoly p)^2 ≤ ENNReal.ofReal A →
        |(∑ i, defectAt (evalPoly p) (z i))/(N : ℝ) - defect (evalPoly p)| ≤ β) := by sorry

end GeoLipLearn.Agnostic
