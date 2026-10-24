-- Prove2me | Theorems.Thm_GenCostSched_GFCS_eq_20
-- name    : GenCostSched.GFCS.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:33.747822+00:00
-- url     : https://prove2.me/theorems/155e5fbc-2e4b-4871-a4d2-04f10052e2c7
-- title:
--   (20), proof of Theorem 3, p. 20 — every optimal dual satisfies β_t ≤ β̂_t, the total increase of the cost functions over the remaining processing
-- statement:
--   Let GFCS(s) be an identical-release instance (jobs $A$ released no later than $s$, positive lengths $\rho_j$, standing assumptions of §II). Let $x$ be an optimal integral schedule of it, and $(\alpha,\beta)$ any optimal solution of its dual. For a time $t$, let
--   $$\hat\beta_t=\sum_{\ell}\int_{(t,\infty)}g'_\ell(\tau)\,x_\ell(\tau)\,d\tau=\sum_{\ell}\sum_{d}\big[g_\ell(C^{2d}_\ell)-g_\ell(C^{2d-1}_\ell)\big],$$
--   where the $[C^{2d-1}_\ell,C^{2d}_\ell)$ are the parts of job $\ell$'s processing after $t$. Then
--   $$\beta_t\ \le\ \hat\beta_t\qquad\text{for almost every }t\ge s .$$
--
--   The paper obtains this from $\beta_t=\partial_tV^o(v^o(t),t)$: delaying the optimal schedule by $\delta$ costs at most $\delta\hat\beta_t+o(\delta)$. The bound lets the analysis replace the optimal β-variables by the explicit upper bounds $\hat\beta$.
--
--   **Formalization Note.** The value function $V^o$ is not formalized; the bound is stated directly between the optimal duals and $\hat\beta$. $\hat\beta$ is defined by the integral form, which is equal to the paper's sum of increments by the fundamental theorem of calculus.
--
--   Differences from the source:
--
--   - generalization: β_t = ∂V^o(v^o(t), t)/∂t, the optimal dual of (13), and the optimal control x^o → every optimal dual (a, β) and every optimal integral schedule x of GFCS(s); reason: the paper's β and x^o are among them, so the statement specializes
--   - encoding: for any t ≥ r_n → for almost every t ≥ s; reason: β is an L¹ density, determined only up to null sets
--   - encoding: β̂_t = Σ_ℓ Σ_d [g_ℓ(C_ℓ^{2d}) − g_ℓ(C_ℓ^{2d−1})] over the processing intervals after t → β̂_t = Σ_ℓ ∫_{(t,∞)} g′_ℓ(τ) x_ℓ(τ) dτ (betaHat); reason: equal by the fundamental theorem of calculus on each interval, as in (23), p. 21; the integral form is defined for every measurable schedule
--   - encoding: the derivative g′_j of g_j on [r_j, ∞) → a given function g' j tied to g j by HasDerivWithinAt (g j) (g' j t) (Ici (r j)) t for t ≥ r_j (JobStanding); reason: g_j is defined and differentiable only on [r_j, ∞) (p. 5), so its derivative there is the within-derivative; supplying it as data changes no instance
-- source:
--   Etesami, An Optimal Control Framework for Online Job Scheduling with General Cost Functions, arXiv:1906.02644v3, p. 20, proof of Theorem 3, display (20) and the sentence after it

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set
open scoped ENNReal

namespace GenCostSched.GFCS

/-- (20) (proof of Theorem 3, p. 20): for an optimal integral schedule `x` of GFCS(s) and every
optimal dual `(a, β)` of the same instance, `β_t ≤ β̂_t` for a.e. `t ≥ s`, where `β̂_t` is the
total increase of the cost functions over the processing of `x` after time `t`. -/
theorem eq_20 {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s) (hρ : ∀ j ∈ A, 0 < ρ j)
    (x : Fin m → ℝ → ℝ) (hx : IsOptIntegral I.g s A ρ x)
    (a : Fin m → ℝ) (β : ℝ → ℝ) (hab : IsOffOptDual I.g s A ρ a β) :
    ∀ᵐ t, s ≤ t → β t ≤ betaHat I.g' x t := by sorry

end GenCostSched.GFCS
