-- Prove2me | Theorems.Thm_NashFlowLT_SteadyState_dual_feasible_phi_le
-- name    : NashFlowLT.SteadyState.dual_feasible_phi_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:29.885014+00:00
-- url     : https://prove2.me/theorems/88c3f89c-ad4c-4d11-a159-716bb86788ca
-- title:
--   Proof of Theorem 3, p. 13 — the labels and queues give a feasible point of (D), so $\Phi(\theta)$ is at most the cost of every feasible point of (P)
-- statement:
--   Let $(f^+,z)$ be a dynamic equilibrium in a fluid queuing network satisfying the standing assumptions, with labels $\ell$ and potential $\Phi$, and let $\theta\ge 0$. Then:
--
--   1. the point $(d,q)$ with
--   $$d_v=\ell_v(\theta)-\ell_s(\theta),\qquad q_e=z_e(\ell_v(\theta))/\nu_e\quad(v \text{ the tail of } e)$$
--   is feasible for the dual program (D): $d_s=0$, $d_w\le d_v+\tau_e+q_e$ for every arc $e=vw$, and $q_e\ge 0$;
--   2. for every feasible point $y'$ of (P),
--   $$\Phi(\theta)\le\sum_{e\in E}\tau_e\,y'_e .$$
--
--   Since $\Phi(\theta)$ is the dual objective $u_0d_t-\sum_e\nu_eq_e$ at this point, weak duality bounds the potential by the optimal value $\alpha$ of (P), uniformly in $\theta$.
--
--   **Formalization Note** The page concludes $\Phi(\theta)\le\alpha$. The formal statement bounds $\Phi(\theta)$ by the cost of every feasible point of (P), which is the same bound and avoids defining $\alpha$ as an infimum.
-- source:
--   Cominetti, Correa & Olver, Long term behavior of dynamic equilibria in fluid queuing networks, arXiv:2112.10412v1, p. 13, proof of Theorem 3; (P), (D) on p. 10

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

namespace NashFlowLT.SteadyState

open MeasureTheory Set Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Proof of Theorem 3, p. 13: at every `θ ≥ 0`, `d_v = ℓ_v(θ) − ℓ_s(θ)`, `q_e = z_e(ℓ_v(θ))/ν_e` is
feasible for (D), and `Φ(θ)` is at most the cost `Σ_e τ_e y_e` of every feasible point `y` of (P). -/
theorem dual_feasible_phi_le (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) (θ : ℝ) (hθ : 0 ≤ θ) :
    IsDualFeasible N (fun v => ell N F v θ - ell N F N.s θ)
        (fun e => F.z e (ell N F (N.tail e) θ) / N.nu e) ∧
      ∀ y : E → ℝ, IsPrimalFeasible N y → Phi N F θ ≤ ∑ e, N.tau e * y e := by sorry
end NashFlowLT.SteadyState
