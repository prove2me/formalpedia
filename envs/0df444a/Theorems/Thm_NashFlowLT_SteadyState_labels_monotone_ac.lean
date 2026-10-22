-- Prove2me | Theorems.Thm_NashFlowLT_SteadyState_labels_monotone_ac
-- name    : NashFlowLT.SteadyState.labels_monotone_ac
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:28.508349+00:00
-- url     : https://prove2.me/theorems/b8444042-ec84-48d1-bf96-526b948cc71c
-- title:
--   §2.3, p. 7 — labels and static flows of a dynamic equilibrium are nondecreasing and absolutely continuous
-- statement:
--   Let $(f^+,z)$ be a dynamic equilibrium in a fluid queuing network satisfying the standing assumptions, with earliest arrival labels $\ell_v(\theta)$ and static flows $x_e(\theta)=F^+_e(\ell_v(\theta))$ ($v$ the tail of $e$). Then:
--
--   1. for every node $v$, $\ell_v$ is nondecreasing on $[0,\infty)$ and absolutely continuous on every interval $[0,T]$, $T\ge 0$;
--   2. for every arc $e$, $x_e$ is nondecreasing on $[0,\infty)$ and absolutely continuous on every interval $[0,T]$, $T\ge 0$.
--
--   In symbols, for $0\le\theta_1\le\theta_2$,
--   $$\ell_v(\theta_1)\le\ell_v(\theta_2),\qquad x_e(\theta_1)\le x_e(\theta_2).$$
--
--   Absolute continuity lets the labels and static flows be recovered from their derivatives by integration, so a dynamic equilibrium is described by the derivatives $\ell'_v$, $x'_e$.
--
--   **Formalization Note** Absolute continuity is Mathlib's `AbsolutelyContinuousOnInterval` on $[0,T]$.
-- source:
--   Cominetti, Correa & Olver, Long term behavior of dynamic equilibria in fluid queuing networks, arXiv:2112.10412v1, p. 7, §2.3

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

namespace NashFlowLT.SteadyState

open MeasureTheory Set Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- §2.3, p. 7: in a dynamic equilibrium the labels `ℓ_v` and the static flows `x_e` are
nondecreasing on `[0, ∞)` and absolutely continuous on every interval `[0, T]`, `T ≥ 0`. -/
theorem labels_monotone_ac (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) :
    (∀ v, MonotoneOn (ell N F v) (Ici 0) ∧
        ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval (ell N F v) 0 T) ∧
      (∀ e, MonotoneOn (staticFlow N F e) (Ici 0) ∧
        ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval (staticFlow N F e) 0 T) := by sorry
end NashFlowLT.SteadyState
