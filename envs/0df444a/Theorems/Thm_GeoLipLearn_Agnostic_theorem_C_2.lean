-- Prove2me | Theorems.Thm_GeoLipLearn_Agnostic_theorem_C_2
-- name    : GeoLipLearn.Agnostic.theorem_C_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:54:15.643197+00:00
-- url     : https://prove2.me/theorems/156d426d-b29b-4ee9-990b-cee2551739de
-- title:
--   Theorem C.2 (Agnostic absolute loss with a known variance bound)
-- statement:
--   There are one training program, one deterministic evaluation program and a universal positive natural constant $C$, chosen before the dimension, parameters and data law. For every dimension $d\ge1$ and any probability law of $(x,y)$ with $x\sim\gamma_d$ and $\operatorname{Var}(y)\le V^2$ for a known $V\ge1$, with arbitrary unknown mean, and $0<\varepsilon\le1$, $0<\delta<1/2$, training returns a finite formula $H$. With probability at least $1-\delta$, simultaneously,
--   $$\operatorname{Lip}(H)\le1,\qquad\operatorname{err}_1(H)\le\operatorname{opt}_1+\varepsilon.$$
--   The infimum defining $\operatorname{opt}_1$ is over all globally 1-Lipschitz functions, without a boundedness restriction. On every stream, sample count, training work and number of representation reals, and on every query the deterministic evaluation work, are at most
--   $$(d+1)^{C(V/\varepsilon)^C}(\log(2/\delta))^3.$$
--   The same two programs serve all parameters and distributions. Evaluation has no access to fresh examples or randomness. This is the variance-bounded agnostic proper-learning goal. The proof on p.49 uses centering and threshold $T_1=18V+\sqrt{2\log(8/\varepsilon)}$; the theorem asserts the existence and complete guarantees of the resulting learner.
--
--   Differences from the source:
--   - encoding: Euclidean space, Gaussian norms, and the norm of the scalar gradient → EuclideanSpace ℝ (Fin d), stdGaussian, extended nonnegative eLpNorm, and the operator norm of fderiv; reason: the scalar derivative has the same norm as the Euclidean gradient; extended norms retain infinity rather than returning a junk zero
--   - encoding: errℓ(f) = E|f(x) − y|^ℓ and optℓ over all 1-Lipschitz functions → nonnegative Lebesgue integrals and an ENNReal infimum over all globally 1-Lipschitz functions; reason: these are the same expectations and comparison class, including unbounded predictors; infinity never becomes zero
--   - encoding: with probability at least 1 − δ → a measurable subset of the specified product probability space, of measure at least ENNReal.ofReal (1 − δ), on which all conclusions hold; reason: this records an actual measurable success event rather than using outer measure of an arbitrary set
--   - reading: there is an algorithm with arithmetic costs and a finite formula, without a specified machine → one rational-literal sampling real-RAM program and one deterministic evaluation program chosen before all parameters and data laws; each run obeys the resource bounds; reason: the machine extends the published core by pointer-to-real, sqrt, exp, log, Gaussian inverse CDF, Gaussian draws and labelled examples; these are the source algorithms primitives, with unit costs except d+1 for an example and no floor or real advice
--   - encoding: return an evaluation procedure and stored numerical data → a finite evaluation program plus a finite block of real memory, whose length and every query evaluation cost are bounded; inputs and output pointers follow the Machine and Learner definitions; reason: this implements the representation convention on p.25 without allowing evaluation access to either random stream or the data law
--   - encoding: (d+1)^{poly(V,1/ε)} (log(2/δ))^3, with B in place of V for C.1 → (d+1)^{C(V/ε)^C} (log(2/δ))^3 for a universal positive natural C; reason: for V≥1 and ε≤1 every fixed polynomial is dominated by C(V/ε)^C; the same C is chosen before d, V, ε, δ and the distribution
--   - encoding: Var(y)≤V² with arbitrary unknown mean → MemLp Prod.snd 2 D and variance Prod.snd D≤V², without a mean input; reason: finite variance in the source includes existence of a finite second moment; MemLp excludes Lean totalization of undefined variance
--   - reading: x ∼ γd on Rd, the dimension d not otherwise restricted → 1 ≤ d; reason: d is the dimension of the Gaussian input space (the paper speaks of polynomial dependence on dimension); ℝ^0 is a single point, where the printed bound (d+1)^{poly}(log 2/δ)^3 = (log 2/δ)^3 admits fewer than 3 instructions and cannot be met (INSIGHTS I1); the brief designates d ≥ 1 as the reading
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p. 48, Theorem C.2

import Definitions.Def_GeoLipLearn_Agnostic_Learner

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

theorem theorem_C_2 : ∃ (P E : Program) (C : ℕ),
    Admissible P ∧ Admissible E ∧ Deterministic E ∧ 0 < C ∧
    ∀ (d : ℕ) (V ε δ : ℝ) (D : Measure (Space d × ℝ)),
      1 ≤ d → IsProbabilityMeasure D → GaussianInput D → VarianceBound D V →
      1 ≤ V → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1/2 →
      Learns P E C d V ε δ D false := by sorry

end GeoLipLearn.Agnostic
