-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_theorem_3_9
-- name    : GaussPolyReg.Approx.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:53.198489+00:00
-- url     : https://prove2.me/theorems/6906c49e-55c5-4cdc-8029-128d5bf5677d
-- title:
--   Theorem 3.9 — multivariate approximation regularity
-- statement:
--   For every $k,D\in\mathbb N$ and $\varepsilon>0$ there is $M=M(k,D,\varepsilon)$ such that the following holds uniformly over all $d_i\le D$ and all $p_i\in H_{d_i}(X)$ with $\mathbb E p_i^2\le1$. There are $m\le M$, positive grades $1\le g_a\le D$, variables $Z_a\in H_{g_a}(X)$, and graded-degree-$d_i$ polynomials $q_i$ in these variables such that
--
--   $$\sum_i\mathbb E|p_i-q_i(Z)|^2\le\varepsilon,\qquad W_2(\operatorname{Law}(Z),N(0,1)^{\otimes m})\le\varepsilon.$$
--
--   The bound is chosen before the degrees and input polynomials. The inputs range over the full countable-variable closed chaos. Constant inputs and $k=0,D=0,m=0$ are retained. This is the multivariate approximation form of regularity.
--
--   Differences from the source:
--   - encoding: functions of the original Gaussian variables, with the closed spans fixed in §2 → L² almost-everywhere classes on the product Gaussian space indexed by ℕ; index n uses coordinates 0 through n−1; reason: reindexing X₁,X₂,… changes no random variable or closed-span instance
--   - encoding: squared L² approximation errors and W₂ → lower Lebesgue integrals and extended nonnegative Wasserstein values on EuclideanSpace; reason: retains infinite errors rather than a default zero and uses the Euclidean metric
--   - encoding: variables with grade g_a ≤ D under the positive-grade convention of §2 → 1 ≤ g_a ≤ D and finite graded Hermite spans for q_i; reason: states the standing positive-grade convention explicitly; in finitely many positive-grade variables a fixed-grade span is finite-dimensional
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Theorem 3.9, p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Chaos

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

theorem theorem_3_9 (k D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ (d : Fin k → ℕ), (∀ i, d i ≤ D) → ∀ p : Fin k → Original,
      (∀ i, p i ∈ chaos (d i)) → (∀ i, ‖p i‖ ^ 2 ≤ 1) →
      ∃ (m : ℕ), m ≤ M ∧ ∃ (g : Fin m → ℕ) (Z : Fin m → Original)
        (q : Fin k → MvPolynomial (Fin m) ℝ),
        (∀ a, 1 ≤ g a ∧ g a ≤ D ∧ Z a ∈ chaos (g a)) ∧
        (∀ i, q i ∈ gradedPolynomials g (d i)) ∧
        (∑ i, squaredError (p i) (q i) Z) ≤ ENNReal.ofReal ε ∧
        wasserstein 2 (vectorLaw Z) (stdGaussian (Vec m)) ≤ ENNReal.ofReal ε := by sorry

end GaussPolyReg.Approx
