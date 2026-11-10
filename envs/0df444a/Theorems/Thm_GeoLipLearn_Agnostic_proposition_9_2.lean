-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_proposition_9_2
-- name    : GeoLipLearn.Agnostic.proposition_9_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:53:41.093883+00:00
-- url     : https://prove2.me/theorems/77d313c6-4f53-4c1d-9118-cea69ca62141
-- title:
--   Proposition 9.2 (Finite Lipschitz correction)
-- statement:
--   There are one admissible correction program, one deterministic evaluation program and a universal positive natural constant $C$ as follows. For $B\ge1$, $0<\tau\le1$, $0<\xi<1/2$, set $r=\tau/64$. Given the coefficients of a degree-at-most-$k$ polynomial $p$ with $\Gamma(p)\le e^{-4/r^4}$, the correction program returns a finite formula $H:\mathbb R^d\to[-B,B]$. With probability at least $1-\xi$,
--   $$\operatorname{Lip}(H)\le1,\qquad\|H-C_B(p)\|_1\le\tau.$$
--   On every random stream its training work, representation size and evaluation work for every query are at most $(d+1)^{C((k+1)/\tau)^C}\,CB^C(\log(2/\xi))^3$. Training may draw Gaussians but cannot request examples; evaluation uses neither source of randomness. This is the finite correction milestone.
--
--   Differences from the source:
--   - encoding: Euclidean space, Gaussian norms, and the norm of the scalar gradient → EuclideanSpace ℝ (Fin d), stdGaussian, extended nonnegative eLpNorm, and the operator norm of fderiv; reason: the scalar derivative has the same norm as the Euclidean gradient; extended norms retain infinity rather than returning a junk zero
--   - encoding: with probability at least 1 − δ → a measurable subset of the specified product probability space, of measure at least ENNReal.ofReal (1 − δ), on which all conclusions hold; reason: this records an actual measurable success event rather than using outer measure of an arbitrary set
--   - reading: there is an algorithm with arithmetic costs and a finite formula, without a specified machine → one rational-literal sampling real-RAM program and one deterministic evaluation program chosen before all parameters and data laws; each run obeys the resource bounds; reason: the machine extends the published core by pointer-to-real, sqrt, exp, log, Gaussian inverse CDF, Gaussian draws and labelled examples; these are the source algorithms primitives, with unit costs except d+1 for an example and no floor or real advice
--   - encoding: return an evaluation procedure and stored numerical data → a finite evaluation program plus a finite block of real memory, whose length and every query evaluation cost are bounded; inputs and output pointers follow the Machine and Learner definitions; reason: this implements the representation convention on p.25 without allowing evaluation access to either random stream or the data law
--   - encoding: normalized Hermite coefficients of degree-at-most-k polynomials → dense monomial coefficients in recursive lexicographic exponent order, with binom(d+k,k) entries; reason: change of basis is polynomial in the polynomial-space dimension, preserving the stated polynomial resource classes and representing every polynomial
--   - encoding: (d+1)^{poly(k,1/τ)} poly(B) (log(2/ξ))^3 → (d+1)^{C((k+1)/τ)^C} CB^C (log(2/ξ))^3 with C universal; reason: positive polynomial majorants have this form for k≥0, B≥1, τ≤1; all three resource clauses are retained
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 34, Proposition 9.2

import Definitions.Def_GeoLipLearn_Agnostic_Learner

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem proposition_9_2 : ∃ (P E : Program) (C : ℕ),
    Admissible P ∧ Admissible E ∧ NoExamples P ∧ Deterministic E ∧ 0 < C ∧
    ∀ (d k : ℕ) (B τ ξ : ℝ) (p : Poly d), p.totalDegree ≤ k →
      1 ≤ B → 0 < τ → τ ≤ 1 → 0 < ξ → ξ < 1/2 →
      defect (evalPoly p) ≤ Real.exp (-4/(τ/64)^4) → Corrects P E C d k B τ ξ p := by sorry

end GeoLipLearn.Agnostic
