-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_theorem_1_1
-- name    : GaussPolyReg.Approx.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:56.120021+00:00
-- url     : https://prove2.me/theorems/20fc52f2-8974-4746-8f52-d20b5869bf83
-- title:
--   Theorem 1.1 — approximation regularity for Gaussian polynomials
-- statement:
--   For every $d\in\mathbb N$ and $\varepsilon>0$ there is $M=M(d,\varepsilon)$ such that for every $p\in H_{\le d}(X)$ with $\mathbb E p^2\le1$ there are $m\le M$, $Z_a\in H_{\le d}(X)$, and a real polynomial $q$ of total degree at most $d$, satisfying
--
--   $$\mathbb E|p-q(Z_1,\ldots,Z_m)|^2\le\varepsilon,\qquad W_2(\operatorname{Law}(Z_1,\ldots,Z_m),N(0,1)^{\otimes m})\le\varepsilon.$$
--
--   The bound is independent of the input polynomial and of how many original coordinates it uses. Both conclusions and the full L² closed chaos over countably many Gaussians are retained. No individual centering or variance-one assumption is imposed on the approximating variables. This is the mission's goal.
--
--   Differences from the source:
--   - encoding: functions of the original Gaussian variables, with the closed spans fixed in §2 → L² almost-everywhere classes on the product Gaussian space indexed by ℕ; index n uses coordinates 0 through n−1; reason: reindexing X₁,X₂,… changes no random variable or closed-span instance
--   - encoding: squared L² approximation errors and W₂ → lower Lebesgue integrals and extended nonnegative Wasserstein values on EuclideanSpace; reason: retains infinite errors rather than a default zero and uses the Euclidean metric
--   - reading: the introduction says span, while §2 defines closed chaos and Theorem 3.9 handles infinitely many variables → the closed span H≤d(X) from §2; reason: uses the paper’s explicit standing definition and includes all finite-variable polynomials together with their L² limits
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Theorem 1.1, p. 1 (conclusions p.2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Chaos

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

theorem theorem_1_1 (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ p : Original, p ∈ chaosLE d → ‖p‖ ^ 2 ≤ 1 →
      ∃ (m : ℕ), m ≤ M ∧ ∃ (q : MvPolynomial (Fin m) ℝ) (Z : Fin m → Original),
        q.totalDegree ≤ d ∧ (∀ a, Z a ∈ chaosLE d) ∧
        squaredError p q Z ≤ ENNReal.ofReal ε ∧
        wasserstein 2 (vectorLaw Z) (stdGaussian (Vec m)) ≤ ENNReal.ofReal ε := by sorry

end GaussPolyReg.Approx
