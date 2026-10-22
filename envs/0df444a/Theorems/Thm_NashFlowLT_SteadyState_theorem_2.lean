-- Prove2me | Theorems.Thm_NashFlowLT_SteadyState_theorem_2
-- name    : NashFlowLT.SteadyState.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:27.026038+00:00
-- url     : https://prove2.me/theorems/8453c2ba-4103-4ce7-b08e-c56f3b291160
-- title:
--   Theorem 2, p. 11 — $\Phi'\ge 0$ wherever it exists, and almost everywhere $\Phi'=0$ exactly when all label derivatives equal 1
-- statement:
--   Let $(f^+,z)$ be a dynamic equilibrium in a fluid queuing network satisfying the standing assumptions, with labels $\ell$ and potential
--   $$\Phi(\theta)=u_0\bigl(\ell_t(\theta)-\ell_s(\theta)\bigr)-\sum_{e\in E}z_e(\ell_v(\theta)).$$
--   At every $\theta>0$ at which $\Phi$ is differentiable, $\Phi'(\theta)\ge 0$. Moreover, for almost every $\theta>0$ the following holds: whenever every label $\ell_v$ is differentiable at $\theta$ with derivative $\ell'_v$ and $\Phi$ is differentiable at $\theta$ with derivative $\Phi'(\theta)$, then
--   $$\Phi'(\theta)=0\iff \ell'_v=1\ \text{for every } v\in V.$$
--
--   The potential is therefore nondecreasing, and it is strictly increasing outside the steady-state regime, which by Lemma 1 is the regime where all label derivatives equal one. This is the Lyapunov argument behind the convergence theorem.
--
--   **Formalization Note** The page states the result "for every $\theta$ that is a point of differentiability of $\Phi$"; its proof takes an NTFR at $\theta$, which exists for almost every $\theta$, and its last lines establish pointwise that $\Phi'(\theta)=0$ iff all $\ell'_v$ equal $1$. The nonnegativity $\Phi'(\theta)\ge 0$ is stated, as on the page, at every point $\theta>0$ of differentiability of $\Phi$; the characterization of $\Phi'(\theta)=0$ keeps the proof's almost-everywhere reading; "unless the dynamic equilibrium has reached a steady state" is linked to the label condition by Lemma 1.
-- source:
--   Cominetti, Correa & Olver, Long term behavior of dynamic equilibria in fluid queuing networks, arXiv:2112.10412v1, pp. 11–12, Theorem 2 and its proof

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

namespace NashFlowLT.SteadyState

open MeasureTheory Set Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Theorem 2, p. 11: at every `θ > 0` at which `Φ` is differentiable, `Φ′(θ) ≥ 0`; and for almost
every `θ > 0`, if the labels are differentiable at `θ` with derivatives `ℓ′` and `Φ` is differentiable
at `θ` with derivative `d`, then `d = 0` exactly when every `ℓ′_v = 1` (the steady-state condition of
Lemma 1). -/
theorem theorem_2 (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) :
    (∀ θ : ℝ, 0 < θ → ∀ d : ℝ, HasDerivAt (Phi N F) d θ → 0 ≤ d) ∧
    ∀ᵐ θ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ (l : V → ℝ) (d : ℝ),
      (∀ v, HasDerivAt (ell N F v) (l v) θ) → HasDerivAt (Phi N F) d θ →
        (d = 0 ↔ ∀ v, l v = 1) := by sorry
end NashFlowLT.SteadyState
