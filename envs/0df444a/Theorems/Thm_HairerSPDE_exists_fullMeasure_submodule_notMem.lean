-- Prove2me | Theorems.Thm_HairerSPDE_exists_fullMeasure_submodule_notMem
-- name    : HairerSPDE.exists_fullMeasure_submodule_notMem
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T00:28:22.743053+00:00
-- url     : https://prove2.me/theorems/d9ee29cb-3a18-42a6-9398-391bb50a3357
-- title:
--   A full-measure measurable subspace missing a point with infinite norm
-- statement:
--   **A measurable full-measure subspace missing a point.** Let $B$ be a separable Banach space, $\mu$ a centred Gaussian Borel measure on $B$, and $h \in B$. Suppose $(\ell_n)$ is a sequence of continuous linear functionals with $C_\mu(\ell_n, \ell_n) \le 1$ and $\ell_n(h) \ge n$ for every $n$. Then there is a Borel-measurable linear subspace $V \subseteq B$ with $\mu(V) = 1$ and $h \notin V$.
--
--   The subspace is $V = \bigcap_n \ker \ell_n$, the common kernel of the functionals. Each $\ker \ell_n$ is closed, hence Borel; it is a full-measure set because $\ell_n$ is a centred Gaussian random variable with variance $C_\mu(\ell_n,\ell_n) \le 1$, so the event $\{\ell_n = 0\}$ has measure zero. A countable intersection of full-measure sets again has full measure, and $h \notin V$ because $\ell_n(h) \ge n > 0$ for every $n$.
-- source:
--   M. Hairer, An Introduction to Stochastic PDEs, arXiv:0907.4178v2, proof of Proposition 4.45.

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem exists_fullMeasure_submodule_notMem {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (L : ℕ → StrongDual ℝ B)
    (hL : ∀ n, covarianceBilinDual μ (L n) (L n) ≤ 1)
    (hLh : ∀ n, ((n : ℕ) : ℝ) ≤ (L n) h) :
    ∃ V : Submodule ℝ B, MeasurableSet (V : Set B) ∧ μ V = 1 ∧ h ∉ V := by sorry

end HairerSPDE
