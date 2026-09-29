-- Prove2me | Theorems.Thm_HairerSPDE_cameronMartinNorm_eq_top
-- name    : HairerSPDE.cameronMartinNorm_eq_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T00:28:21.866513+00:00
-- url     : https://prove2.me/theorems/b7566218-8723-40c9-bb39-b07af4a9196d
-- title:
--   Infinite Cameron-Martin norm yields unbounded dual witnesses
-- statement:
--   **Unbounded dual witnesses from an infinite Cameron-Martin norm.** Let $B$ be a separable Banach space and $\mu$ a centred Gaussian Borel measure on $B$. If $h \in B$ has infinite Cameron-Martin norm, $\|h\|_\mu = \infty$, then there is a sequence $(\ell_n)_{n \in \mathbb{N}}$ of continuous linear functionals with $C_\mu(\ell_n, \ell_n) \le 1$ for every $n$ and $\ell_n(h) \ge n$ for every $n$.
--
--   This is the unwinding of the defining supremum $\|h\|_\mu = \sup\{\ell(h) : C_\mu(\ell,\ell) \le 1\}$: the value $\infty$ means the set of admissible values is unbounded above, so admissible functionals with arbitrarily large value at $h$ exist. The sequence produced here is the input to the construction of a measurable full-measure subspace missing $h$.
-- source:
--   M. Hairer, An Introduction to Stochastic PDEs, arXiv:0907.4178v2, Exercise 4.38 and the construction in Proposition 4.45.

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem cameronMartinNorm_eq_top {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (hh : cameronMartinNorm μ h = ∞) :
    ∃ L : ℕ → StrongDual ℝ B,
      (∀ n, covarianceBilinDual μ (L n) (L n) ≤ 1) ∧ (∀ n, ((n : ℕ) : ℝ) ≤ (L n) h) := by sorry

end HairerSPDE
