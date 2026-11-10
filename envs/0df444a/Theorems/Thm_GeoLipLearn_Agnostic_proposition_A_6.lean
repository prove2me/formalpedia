-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_proposition_A_6
-- name    : GeoLipLearn.Agnostic.proposition_A_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:53:49.40768+00:00
-- url     : https://prove2.me/theorems/3519a505-1a04-4849-b0d7-0c640af0f324
-- title:
--   Proposition A.6 (Polynomial learning for bounded agnostic labels)
-- statement:
--   For either loss exponent $\ell\in\{1,2\}$, Gaussian inputs, arbitrary almost-surely bounded labels $|y|\le B$ with $B\ge1$, and $0<\eta,\alpha,\zeta\le1$, one uniform algorithm returns a polynomial $p$ such that, with probability at least $1-\zeta$,
--   $$\operatorname{err}_\ell(p)\le\operatorname{opt}_\ell+\eta,\qquad\Gamma(p)\le\alpha^2,\qquad\|p\|_2\le B.$$
--   Its degree bound is Equation (25) with parameters $\eta/2,\alpha/2$. Writing $D=\binom{d+k}{k}$, its sample and arithmetic work bounds on every stream are $C(1+B+\eta^{-1}+\alpha^{-1}+k+D+9^k)^C(\log(2/\zeta))^2$, with universal positive natural $C$. The output lists the coefficients in the shared monomial convention. This is the agnostic polynomial-learning milestone for both losses.
--
--   Differences from the source:
--   - encoding: Euclidean space, Gaussian norms, and the norm of the scalar gradient → EuclideanSpace ℝ (Fin d), stdGaussian, extended nonnegative eLpNorm, and the operator norm of fderiv; reason: the scalar derivative has the same norm as the Euclidean gradient; extended norms retain infinity rather than returning a junk zero
--   - encoding: errℓ(f) = E|f(x) − y|^ℓ and optℓ over all 1-Lipschitz functions → nonnegative Lebesgue integrals and an ENNReal infimum over all globally 1-Lipschitz functions; reason: these are the same expectations and comparison class, including unbounded predictors; infinity never becomes zero
--   - encoding: with probability at least 1 − δ → a measurable subset of the specified product probability space, of measure at least ENNReal.ofReal (1 − δ), on which all conclusions hold; reason: this records an actual measurable success event rather than using outer measure of an arbitrary set
--   - reading: there is an algorithm with arithmetic costs, without a specified machine → one rational-literal sampling real-RAM program chosen before all parameters and data laws; on every stream it halts within the resource bound and writes the binom(d+k,k) output coefficients; reason: the machine extends the published core by pointer-to-real, sqrt, exp, log, Gaussian inverse CDF, Gaussian draws and labelled examples; these are the source algorithms primitives, with unit costs except d+1 for an example and no floor or real advice
--   - encoding: normalized Hermite coefficients of degree-at-most-k polynomials → dense monomial coefficients in recursive lexicographic exponent order, with binom(d+k,k) entries; reason: change of basis is polynomial in the polynomial-space dimension, preserving the stated polynomial resource classes and representing every polynomial
--   - encoding: universal polynomial P(B,η⁻¹,α⁻¹,k,D,9^k) → C(1+B+η⁻¹+α⁻¹+k+D+9^k)^C for universal C>0; reason: a polynomial majorant is equivalent on these nonnegative parameter ranges; both sample and work clauses are retained
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 41, Proposition A.6

import Definitions.Def_GeoLipLearn_Agnostic_Learner

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem proposition_A_6 : ∃ (P : Program) (C : ℕ),
    Admissible P ∧ 0 < C ∧ ∀ (d ell : ℕ) (B η α ζ : ℝ)
      (D : Measure (Space d × ℝ)), IsProbabilityMeasure D → GaussianInput D →
      BoundedLabels D B → 1 ≤ B → (ell = 1 ∨ ell = 2) →
      0 < η → η ≤ 1 → 0 < α → α ≤ 1 → 0 < ζ → ζ ≤ 1 →
      PolynomialLearns P C d ell B η α ζ D := by sorry

end GeoLipLearn.Agnostic
