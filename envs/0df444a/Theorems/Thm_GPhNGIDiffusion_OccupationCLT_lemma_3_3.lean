-- Prove2me | Theorems.Thm_GPhNGIDiffusion_OccupationCLT_lemma_3_3
-- name    : GPhNGIDiffusion.OccupationCLT.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:06.550934+00:00
-- url     : https://prove2.me/theorems/335d201c-3a47-4a80-a0a0-73f80157ccf3
-- title:
--   Lemma 3.3, p. 13 — Bismut–Elworthy–Li formula ∇_u E[ψ(X^x_t)] = E[ψ(X^x_t)𝓘^x_u(t)]
-- statement:
--   Let $\psi\in C^1(\mathbb R^d,\mathbb R)$ with $\|\nabla\psi\|_\infty<\infty$. For every $t>0$ and $x,u\in\mathbb R^d$, the directional derivative of $y\mapsto\mathbb E[\psi(X^y_t)]$ at $x$ in the direction $u$ exists and
--   $$
--   \nabla_u\mathbb E[\psi(X^x_t)]=\mathbb E[\psi(X^x_t)\,\mathcal I^x_u(t)],
--   $$
--   where $\mathcal I^x_u(t)=\frac1t\int_0^t\langle\sigma^{-1}J^x_ru,dB_r\rangle$ (3.14).
--
--   The formula expresses the derivative of the semigroup without differentiating $\psi$, which is what lets the gradient of the Stein solution be bounded for bounded measurable data.
--
--   **Formalization Note** $\nabla_u$ is the directional derivative of §1.4, rendered as `HasLineDerivAt`, which asserts existence as well as the value. $J^x$ is the propagator (see the `Jacobian` definition).
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 13, Lemma 3.3 (proof p. 34)

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Diffusion
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Jacobian
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Ito
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GPhNGIDiffusion.OccupationCLT

/-- Lemma 3.3, p. 13 (Bismut–Elworthy–Li type formula). Let `ψ ∈ C¹(ℝᵈ, ℝ)` with
`∥∇ψ∥_∞ < ∞`. For every `t > 0` and `x, u ∈ ℝᵈ`, the directional derivative of
`y ↦ E[ψ(X^y_t)]` at `x` in direction `u` exists and equals `E[ψ(X^x_t) I^x_u(t)]`, where
`I^x_u(t) = (1/t)∫₀ᵗ⟨σ⁻¹J^x_r u, dB_r⟩` (3.14) and `J^x` is the propagator of
`∂ₜJ = ∇g̃(X^x_t)J`. -/
theorem lemma_3_3 {d : ℕ} (M : Model d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → E d) (X : E d → ℝ≥0 → Ω → E d) (hX : IsDiffusion M P B X)
    (J : E d → ℝ≥0 → ℝ≥0 → Ω → (E d →L[ℝ] E d))
    (hJ : ∀ x ω, IsPropagator (fun r => M.gradTilde (X x r ω)) (fun s t => J x s t ω))
    (ψ : E d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψ' : ∃ K : ℝ, ∀ y, ‖fderiv ℝ ψ y‖ ≤ K)
    (t : ℝ≥0) (ht : 0 < t) (x u : E d) (I : Ω → ℝ)
    (hI : IsItoIntegral P B (fun r ω => mat M.σ⁻¹ (J x 0 r ω u)) t I) :
    HasLineDerivAt ℝ (fun y => ∫ ω, ψ (X y t ω) ∂P)
      (∫ ω, ψ (X x t ω) * ((t : ℝ)⁻¹ * I ω) ∂P) x u := by sorry

end GPhNGIDiffusion.OccupationCLT
