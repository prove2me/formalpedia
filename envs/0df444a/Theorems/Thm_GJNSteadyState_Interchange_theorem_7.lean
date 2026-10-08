-- Prove2me | Theorems.Thm_GJNSteadyState_Interchange_theorem_7
-- name    : GJNSteadyState.Interchange.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:48.267709+00:00
-- url     : https://prove2.me/theorems/6023b027-b39a-43c5-8c53-b308c27364b5
-- title:
--   Theorem 7, p. 17 — uniform exponential tail of the scaled stationary workload n^{−1/2}w′Qⁿ(0)
-- statement:
--   Let $\Xi^n$ be the heavy-traffic sequence built from a critically loaded GJN $\Xi$ and $\kappa^0>0$, and $w=e'[I-P']^{-1}$. There exist constants $C_1,c_1>0$, depending only on $\Xi$, such that for all sufficiently large $n$ every stationary distribution $\pi^n$ of $\Xi^n$ satisfies
--   $$\mathbb P_{\pi^n}\big(n^{-1/2}w'Q^n(0)>s\big)\le C_1e^{-c_1s}\qquad\text{for all }s>0. \tag{35}$$
--
--   Since $1-\rho^{*n}=\kappa^*/\sqrt n$, each queue $Q^n_j$ is of order $(1-\rho^{*n})^{-1}$ in steady state, uniformly in $n$; this is the tightness behind Corollary 1.
--
--   **Formalization Note** The constants are quantified before $n$ and before the stationary distributions; the bound holds for every stationary distribution of $\Xi^n$, unique or not.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 17, Theorem 7, (35)

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Network
import Definitions.Def_GJNSteadyState_Interchange_Dynamics
import Definitions.Def_GJNSteadyState_Interchange_HeavyTraffic
open MeasureTheory Filter Topology Matrix

namespace GJNSteadyState.Interchange

/-- Theorem 7 (p. 17): there are `C₁, c₁ > 0` depending only on `Ξ` such that, for all large
`n`, every stationary distribution `πⁿ` of `Ξⁿ` satisfies
(35) `P_{πⁿ}(n^{−1/2} w′Qⁿ(0) > s) ≤ C₁ exp(−c₁ s)` for all `s > 0`. -/
theorem theorem_7 {J : ℕ} (Ξ : Network J) (hΞ : Ξ.IsGJN) (hcrit : IsCritical Ξ)
    (κ0 : Fin J → ℝ) (hκ0 : ∀ j, 0 < κ0 j) :
    ∃ C₁ c₁ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ π : Measure (State J), IsStationary (htNet Ξ κ0 n) π → ∀ s : ℝ, 0 < s →
        π {x | s < (Real.sqrt n)⁻¹ * (wvec Ξ ⬝ᵥ fun j => (x.1 j : ℝ))} ≤
          ENNReal.ofReal (C₁ * Real.exp (-(c₁ * s))) := by sorry

end GJNSteadyState.Interchange
