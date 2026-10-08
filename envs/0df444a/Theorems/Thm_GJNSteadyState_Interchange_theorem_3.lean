-- Prove2me | Theorems.Thm_GJNSteadyState_Interchange_theorem_3
-- name    : GJNSteadyState.Interchange.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:47.915994+00:00
-- url     : https://prove2.me/theorems/98bb0b58-ecd7-4b84-a24c-77da1c29e05f
-- title:
--   Theorem 3, p. 13 (existence and uniqueness) — the RBM has a stationary distribution iff [I − P′]⁻¹β < 0, and it is unique
-- statement:
--   Let $P$ be a substochastic $J\times J$ matrix with spectral radius less than one, $\beta\in\mathbb R^J$ and $\Gamma$ a positive definite covariance matrix. The reflected Brownian motion with parameters $(\beta,\Gamma,I-P')$ possesses a stationary distribution $\pi_{\mathrm{RBM}}$ if and only if
--   $$[I-P']^{-1}\beta<0\quad\text{(componentwise)}.$$
--   When this distribution exists, it is unique.
--
--   Applied with the $\beta$ of Theorem 4, for which $[I-P']^{-1}\beta=-M^{-1}\kappa<0$ (Remark 4), it gives the object $\pi_{\mathrm{RBM}}$ of Theorem 8.
--
--   **Formalization Note** Only the first two sentences of Theorem 3 are stated; the convergence of marginals to $\pi_{\mathrm{RBM}}$ is not used by Theorem 8. Positive definiteness of $\Gamma$ is the hypothesis of Harrison and Williams (1987), from whom the page cites the result; the page does not state it.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 13, Theorem 3 (cited: Harrison and Williams 1987)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_GJNSteadyState_Interchange_RBM
open MeasureTheory Filter Topology Matrix

namespace GJNSteadyState.Interchange

/-- Theorem 3 (p. 13, Harrison–Williams), existence and uniqueness: for a substochastic `P`
with spectral radius `< 1` and a positive definite covariance `Γ`, the `(β, Γ, I − P′)`-RBM has
a stationary distribution if and only if `[I − P′]⁻¹β < 0` (componentwise), and it has at most
one. -/
theorem theorem_3 {J : ℕ} (P : Matrix (Fin J) (Fin J) ℝ) (hP0 : ∀ j k, 0 ≤ P j k)
    (hP1 : ∀ j, ∑ k, P j k ≤ 1) (hPm : Tendsto (fun m : ℕ => P ^ m) atTop (𝓝 0))
    (β : Fin J → ℝ) (Γ : Matrix (Fin J) (Fin J) ℝ) (hΓ : Γ.PosDef) :
    ((∃ ν : Measure (Fin J → ℝ), IsRBMStationary P β Γ ν) ↔
        ∀ j, ((1 - Pᵀ)⁻¹ *ᵥ β) j < 0) ∧
      ∀ ν ν' : Measure (Fin J → ℝ), IsRBMStationary P β Γ ν → IsRBMStationary P β Γ ν' →
        ν = ν' := by sorry

end GJNSteadyState.Interchange
