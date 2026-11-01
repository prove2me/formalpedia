-- Prove2me | Theorems.Thm_NashFlowLT_SteadyState_steady_phase_persists
-- name    : NashFlowLT.SteadyState.steady_phase_persists
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T09:24:31.645978+00:00
-- url     : https://prove2.me/theorems/a17dd084-86db-46ad-a713-2b5410c6dcfb
-- title:
--   p. 8 / proof of Theorem 3, p. 12 — a steady-state phase lasts forever
-- statement:
--   Let a fluid queuing network satisfy the standing assumptions and let $(f^+,z)$ be a dynamic equilibrium with labels $\ell_v$. A steady-state phase lasts forever: if $0\le a<b$ and
--   $$\ell_v'(\theta)=1\qquad\text{for every } v\in V \text{ and every } \theta\in(a,b),$$
--   then $\ell_v$ is differentiable with $\ell_v'(\theta)=1$ for every $v\in V$ and every $\theta>a$.
--
--   In a phase with all $\ell'_v=1$ the differences $\ell_w-\ell_v$ are constant, so the active arcs $E'_\theta$ and queue arcs $E^*_\theta$ do not change and the same normalized thin flow with resetting (whose $\ell'$-component is unique, p. 7) keeps being the derivative; the source uses this when it says of Example 1 that the final phase "constitute[s] a steady state so it lasts forever" (p. 8), and implicitly in the proof of Theorem 3 (p. 12), where a non-steady phase must have $\Phi'\ge\kappa$ and a reached steady state is never left.
-- source:
--   Cominetti, Correa & Olver, Long term behavior of dynamic equilibria in fluid queuing networks, arXiv:2112.10412v1, p. 8 (Example 1: "This last phase constitute a steady state so it lasts forever") and proof of Theorem 3, p. 12

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

namespace NashFlowLT.SteadyState

open MeasureTheory Set Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- p. 8 and proof of Theorem 3, p. 12: a steady-state phase lasts forever. If on some open interval
`(a, b)`, `0 ≤ a < b`, every label has derivative `1`, then every label has derivative `1` at every
time `θ > a`. -/
theorem steady_phase_persists (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (h : ∀ v, ∀ θ ∈ Ioo a b, HasDerivAt (ell N F v) 1 θ) :
    ∀ v θ, a < θ → HasDerivAt (ell N F v) 1 θ := by sorry

end NashFlowLT.SteadyState
