-- Prove2me | Theorems.Thm_FrieszDUE_PIE_ess_inf_lower_bound_17
-- name    : FrieszDUE.PIE.ess_inf_lower_bound_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:19:34.782143+00:00
-- url     : https://prove2.me/theorems/6413320a-47c4-4d35-b61f-19a85ea3b0ac
-- title:
--   Proof of Theorem 2 part ii, p. 187 — C_p(t, h) ≥ μ_p(h) ≥ μ_kl(h) for ν-a.a. t: (17) holds by construction
-- statement:
--   In the setting of the PIE model, let $T>0$, let $h$ be a density vector, and suppose that for every path $p$ the cost $C_p(\cdot,h)$ is nonnegative on $[0,T]$ and measurable. Then for every OD pair $kl$, every path $p\in P_{kl}$ and $\nu$-almost all $t$,
--
--   $$C_p(t,h)\ \ge\ \mu_p(h)\ \ge\ \mu_{kl}(h),$$
--
--   where $\mu_p(h)$ is the essential infimum (14) of $C_p(\cdot,h)$ on $[0,T]$ and $\mu_{kl}(h)$ is the minimum (15) over $P_{kl}$.
--
--   With $h=h^*$ and $\mu^*_{kl}=\mu_{kl}(h^*)$, this says that the pair $(h^*,\mu^*)$ satisfies condition (17) of Definition 3 by construction.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 187, proof of Theorem 2 part ii, display after the definition of μ*, with (12), (14), (15), (17)

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

namespace FrieszDUE.PIE

open MeasureTheory

/-- Proof of Theorem 2 part ii, p. 187: (17) holds by construction for `μ_kl(h)`. -/
theorem ess_inf_lower_bound_17 {P W : Type*}
    (T : ℝ) (hT : 0 < T) (od : P → W) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (h : P → ℝ → ℝ)
    (hC_nonneg : ∀ p, ∀ t ∈ Set.Icc 0 T, 0 ≤ C p t h)
    (hC_meas : ∀ p, AEMeasurable (fun t => C p t h) (ν T)) (p : P) :
    ∀ᵐ t ∂(ν T), muPath T C h p ≤ C p t h ∧ muOD T od C h (od p) ≤ muPath T C h p := by sorry

end FrieszDUE.PIE
