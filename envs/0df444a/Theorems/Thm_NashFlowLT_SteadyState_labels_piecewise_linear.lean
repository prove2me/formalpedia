-- Prove2me | Theorems.Thm_NashFlowLT_SteadyState_labels_piecewise_linear
-- name    : NashFlowLT.SteadyState.labels_piecewise_linear
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T09:24:43.17999+00:00
-- url     : https://prove2.me/theorems/9a1096ef-2517-406b-8051-d6ff247ad936
-- title:
--   §2.3, p. 8 — the labels $\ell_v$ of a dynamic equilibrium are piecewise linear (every $\theta\ge0$ starts a linear phase)
-- statement:
--   Let a fluid queuing network satisfy the standing assumptions ($\nu_e>0$, $\tau_e\ge0$, $u_0>0$, $s\ne t$, every node reachable from $s$) and let $(f^+,z)$ be a dynamic equilibrium with earliest-arrival labels $\ell_v(\theta)$. The labels are piecewise linear, evolving in phases: for every $\theta\ge 0$ there are $\varepsilon>0$ and slopes $(c_v)_{v\in V}$ such that
--   $$\ell_v(\theta')=\ell_v(\theta)+c_v\,(\theta'-\theta)\qquad\text{for all } v\in V,\ \theta'\in[\theta,\theta+\varepsilon].$$
--
--   This is the statement on p. 8 of the source: since the derivatives $\ell'$ are the (unique) $\ell'$-component of the normalized thin flow with resetting for the current pair $E^*_\theta\subseteq E'_\theta$, of which there are finitely many options, "the functions $\ell_v(\theta)$ will be uniquely defined and piecewise linear with finitely many options for the derivatives" (existence/uniqueness of ntfr from Cominetti, Correa and Larré 2015; phase-by-phase integration from Koch and Skutella 2011). **Formalization note:** "piecewise linear" is expressed as: every time $\theta\ge0$ is the left end of a nondegenerate interval on which all labels are affine (each phase extends to the right by a positive amount).
-- source:
--   Cominetti, Correa & Olver, Long term behavior of dynamic equilibria in fluid queuing networks, arXiv:2112.10412v1, p. 8 (§2.3, paragraph after (13): labels are piecewise linear with finitely many options for the derivatives)

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

namespace NashFlowLT.SteadyState

open MeasureTheory Set Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- §2.3, p. 8: the labels of a dynamic equilibrium are piecewise linear, i.e. evolve in phases:
every time `θ ≥ 0` starts a phase `[θ, θ + ε]`, `ε > 0`, on which every label `ℓ_v` is affine with
some slope `c_v`. -/
theorem labels_piecewise_linear (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) :
    ∀ θ : ℝ, 0 ≤ θ → ∃ ε : ℝ, 0 < ε ∧ ∃ c : V → ℝ,
      ∀ v, ∀ θ' ∈ Icc θ (θ + ε), ell N F v θ' = ell N F v θ + c v * (θ' - θ) := by sorry

end NashFlowLT.SteadyState
