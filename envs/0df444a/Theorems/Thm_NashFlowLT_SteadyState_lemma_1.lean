-- Prove2me | Theorems.Thm_NashFlowLT_SteadyState_lemma_1
-- name    : NashFlowLT.SteadyState.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:22.477382+00:00
-- url     : https://prove2.me/theorems/5d4f160b-621a-4f3e-8058-b182250be76f
-- title:
--   Lemma 1, p. 9 — a dynamic equilibrium attains a steady state iff all label derivatives are eventually 1
-- statement:
--   Let $(f^+,z)$ be a dynamic equilibrium in a fluid queuing network satisfying the standing assumptions, with labels $\ell$. The following are equivalent:
--
--   1. the equilibrium attains a steady state: there is $\theta_0\ge 0$ such that $z_e(\theta)=z_e(\theta_0)$ for every arc $e$ and every $\theta\ge\theta_0$;
--   2. there is $\theta^*\ge 0$ such that every label is differentiable with derivative one after $\theta^*$:
--   $$\ell'_v(\theta)=1\qquad\text{for every } v\in V \text{ and every } \theta>\theta^*.$$
--
--   The lemma translates the steady state, a statement about queues in real time, into the label condition used by the potential argument of Theorems 2 and 3.
--
--   **Formalization Note** The page writes "for all $\theta\ge\theta^*$". The formal statement uses $\theta>\theta^*$ with two-sided derivatives, because a two-sided derivative need not exist at the time the steady state starts; the two readings yield the same steady states (shift $\theta^*$).
-- source:
--   Cominetti, Correa & Olver, Long term behavior of dynamic equilibria in fluid queuing networks, arXiv:2112.10412v1, p. 9, Lemma 1

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

namespace NashFlowLT.SteadyState

open MeasureTheory Set Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Lemma 1, p. 9: a dynamic equilibrium attains a steady state iff from some time `θ* ≥ 0` on every
label has derivative `1`. -/
theorem lemma_1 (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) :
    AttainsSteadyState N F ↔
      ∃ θs : ℝ, 0 ≤ θs ∧ ∀ v θ, θs < θ → HasDerivAt (ell N F v) 1 θ := by sorry
end NashFlowLT.SteadyState
