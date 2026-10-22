-- Prove2me | Theorems.Thm_NashFlowLT_SteadyState_queue_identity
-- name    : NashFlowLT.SteadyState.queue_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:35.2536+00:00
-- url     : https://prove2.me/theorems/16486cde-e475-4f69-9d50-122e1a8c2b38
-- title:
--   Proof of Theorem 2, p. 11 — in a dynamic equilibrium, $z_e(\ell_v(\theta))=\nu_e[\ell_w(\theta)-\ell_v(\theta)-\tau_e]_+$
-- statement:
--   Let $(f^+,z)$ be a dynamic equilibrium in a fluid queuing network satisfying the standing assumptions, with labels $\ell$. For every arc $e=vw$ and every $\theta\ge 0$,
--   $$z_e(\ell_v(\theta))=\nu_e\,\bigl[\ell_w(\theta)-\ell_v(\theta)-\tau_e\bigr]_+ ,$$
--   where $[a]_+=\max\{a,0\}$.
--
--   The queue seen on arrival at the tail of an arc is thus a function of the labels alone. This rewrites the potential $\Phi$ in terms of labels and is the starting point of the derivative computation in Theorem 2.
-- source:
--   Cominetti, Correa & Olver, Long term behavior of dynamic equilibria in fluid queuing networks, arXiv:2112.10412v1, p. 11, proof of Theorem 2

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

namespace NashFlowLT.SteadyState

open MeasureTheory Set Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Proof of Theorem 2, p. 11: in a dynamic equilibrium, for every arc `e = vw` and every `θ ≥ 0`,
`z_e(ℓ_v(θ)) = ν_e [ℓ_w(θ) − ℓ_v(θ) − τ_e]₊`. -/
theorem queue_identity (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) :
    ∀ e θ, 0 ≤ θ → F.z e (ell N F (N.tail e) θ) =
      N.nu e * max (ell N F (N.head e) θ - ell N F (N.tail e) θ - N.tau e) 0 := by sorry
end NashFlowLT.SteadyState
