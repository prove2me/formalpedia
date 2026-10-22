-- Prove2me | Theorems.Thm_NashFlowLT_SteadyState_derivatives_ntfr
-- name    : NashFlowLT.SteadyState.derivatives_ntfr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:25.643009+00:00
-- url     : https://prove2.me/theorems/1acad073-c131-47ee-99f0-c14f89a396f7
-- title:
--   §2.3, p. 7, (10)–(13) — almost everywhere, the derivatives of a dynamic equilibrium form a normalized thin flow with resetting
-- statement:
--   Let $(f^+,z)$ be a dynamic equilibrium in a fluid queuing network satisfying the standing assumptions. For almost every $\theta>0$ there are $\ell'\in\mathbb R^V$ and $x'\in\mathbb R^E$ such that
--
--   1. every label $\ell_v$ is differentiable at $\theta$ with derivative $\ell'_v$;
--   2. every static flow $x_e=F^+_e\circ\ell_v$ is differentiable at $\theta$ with derivative $x'_e$;
--   3. $(\ell',x')$ is a normalized thin flow with resetting for the active arcs $E'_\theta$ and the queue arcs $E^*_\theta$, that is, $E^*_\theta\subseteq E'_\theta$, $\ell',x'\ge 0$, $x'$ is an $st$-flow of value $u_0$, and
--   $$\ell'_s=1,\qquad \ell'_w=\min_{e=vw\in E'_\theta}\rho_e(\ell'_v,x'_e)\ (w\ne s),\qquad \rho_e(\ell'_v,x'_e)=\begin{cases}x'_e/\nu_e & e\in E^*_\theta\\ \max\{\ell'_v,x'_e/\nu_e\} & e\notin E^*_\theta,\end{cases}$$
--   with $x'_e>0\Rightarrow\ell'_w=\rho_e(\ell'_v,x'_e)$ on $E'_\theta$ and $x'_e=0$ off $E'_\theta$.
--
--   This is the local characterization of dynamic equilibria: their evolution is driven by thin flows computed on the current shortest-path network.
--
--   **Formalization Note** The page says "let $\theta$ be a point of differentiability"; the footnote states the derivatives exist almost everywhere. The statement is posed for almost every $\theta>0$ (Lebesgue measure), the set on which the page's derivation applies.
-- source:
--   Cominetti, Correa & Olver, Long term behavior of dynamic equilibria in fluid queuing networks, arXiv:2112.10412v1, p. 7, §2.3, eqs. (10)–(13)

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

namespace NashFlowLT.SteadyState

open MeasureTheory Set Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- §2.3, p. 7, (10)–(13): for almost every `θ > 0` the labels and static flows of a dynamic
equilibrium are differentiable at `θ` and their derivatives `(ℓ′, x′)` form a normalized thin flow with
resetting for the active arcs `E′_θ` and the queue arcs `E*_θ`. -/
theorem derivatives_ntfr (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) :
    ∀ᵐ θ ∂(volume.restrict (Ioi (0 : ℝ))), ∃ (l : V → ℝ) (x : E → ℝ),
      (∀ v, HasDerivAt (ell N F v) (l v) θ) ∧
      (∀ e, HasDerivAt (staticFlow N F e) (x e) θ) ∧
      IsNTFR N {e | IsActive N F e θ} {e | HasQueue N F e θ} l x := by sorry
end NashFlowLT.SteadyState
