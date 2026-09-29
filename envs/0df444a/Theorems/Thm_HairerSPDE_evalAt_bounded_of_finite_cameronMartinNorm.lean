-- Prove2me | Theorems.Thm_HairerSPDE_evalAt_bounded_of_finite_cameronMartinNorm
-- name    : HairerSPDE.evalAt_bounded_of_finite_cameronMartinNorm
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T12:17:17.939533+00:00
-- url     : https://prove2.me/theorems/61b3bc2d-5d99-4283-b95b-61b49803eed1
-- title:
--   Bounded dual evaluation from a finite Cameron-Martin norm
-- statement:
--   **Bounded dual evaluation from a finite Cameron-Martin norm.** Let $B$ be a separable Banach space, $\mu$ a centred Gaussian Borel measure on $B$, and $h \in B$ with $\|h\|_\mu \neq \infty$. Then evaluation at $h$ is bounded on the duals in the $L^2(\mu)$ seminorm: there is $C \ge 0$ with $|\ell(h)| \le C\,\|\ell\|_{L^2(\mu)}$ for every $\ell \in B^*$. This is the scaling argument in Hairer's Exercise 4.38: with $S = \|h\|_\mu < \infty$, each $\ell$ with $C_\mu(\ell,\ell) \le 1$ satisfies $\ell(h) \le S$, and homogeneity (using $C_\mu(\ell,\ell) = \|\ell\|_{L^2}^2$ for centred $\mu$) extends the bound to all of $B^*$, with the zero-variance case forcing $\ell(h) = 0$ by considering $s\ell$ for all $s > 0$.
-- source:
--   M. Hairer, An Introduction to Stochastic PDEs, arXiv:0907.4178v2, Section 4.2, Exercise 4.38 (the Cameron-Martin norm as an operator norm), used in the proof of Proposition 4.45, p. 32.

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem evalAt_bounded_of_finite_cameronMartinNorm {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (hh : cameronMartinNorm μ h ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : StrongDual ℝ B, |L h| ≤ C * (eLpNorm (fun x => L x) 2 μ).toReal := by sorry

end HairerSPDE
