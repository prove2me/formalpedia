-- Prove2me | Theorems.Thm_HighDimStat_Decomposability_prop9_13_basic_inequality
-- name    : HighDimStat.Decomposability.prop9_13_basic_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:16:01.40038+00:00
-- url     : https://prove2.me/theorems/ec1843c4-02d5-4e1f-8d5c-d7cdec04cb41
-- title:
--   Decomposability confines the M-estimator error to a cone (Proposition 9.13)
-- statement:
--   **Proposition 9.13.** Decomposability of the regularizer, together with the good event
--   $\mathcal G(\lambda_n)$, forces the M-estimator's error vector into an explicit geometric
--   set — without any further probabilistic argument.
--
--   Let $L_n:\Omega\to\mathbb R$ be convex, let $\Phi:\Omega\to[0,\infty)$ be a norm, decomposable
--   with respect to a subspace pair $(\mathcal M,\bar{\mathcal M})$, and let $\hat\theta$ be any
--   optimal solution of the regularized M-estimator $\min_\theta L_n(\theta)+\lambda_n\Phi(\theta)$
--   (with $\lambda_n>0$), with score $g=\nabla L_n(\theta^*)$. Conditioned on the good event
--   $\mathcal G(\lambda_n)=\{\Phi^*(g)\le\lambda_n/2\}$, the error $\Delta=\hat\theta-\theta^*$
--   belongs to the set
--
--   $$
--   \mathbb C_{\theta^*}(\mathcal M,\bar{\mathcal M}) := \Big\{\Delta\in\Omega \;\Big|\;
--   \Phi(\Delta_{\bar{\mathcal M}^\perp}) \le 3\Phi(\Delta_{\bar{\mathcal M}}) +
--   4\Phi(\theta^*_{\mathcal M^\perp})\Big\}.
--   $$
--
--   This is the chapter's foundational structural result: it converts the optimality of
--   $\hat\theta$, together with the regularizer's decomposability, into a purely geometric
--   confinement of the error to a cone-like set, before any curvature condition is invoked.
--
--   **Formalization Note** Stated as membership of `θhat - θstar` in `errorCone Φ M Mbar θstar`
--   — the definitions file's direct transcription of Eq. (9.29) — rather than restating the cone
--   inline. `hopt` packages "$\hat\theta$ is a global optimum of $L_n+\lambda_n\Phi$" directly
--   (the basic-inequality argument the book's own proof (p. 274) uses is via this optimality, not
--   via a subgradient characterization).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 273 (PDF p. 293), Proposition 9.13, Eq. (9.29)

import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

/-- Proposition 9.13 (p. 273, "a key consequence of decomposability"): let `Ln` be convex with
score `g = ∇Ln(θ*)`, `Φ` a norm decomposable with respect to `(M, M̄)`, and `θ̂` any optimal
solution of the regularized M-estimator `min_θ Ln(θ) + λn Φ(θ)`. Conditioned on the good event
`G(λn) = {Φ*(g) ≤ λn/2}`, the error `Δ = θ̂ - θ*` lies in the cone `C_{θ*}(M, M̄)`. -/
theorem prop9_13_basic_inequality
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN) :
    θhat - θstar ∈ errorCone Φ M Mbar θstar := by sorry

end HighDimStat.Decomposability
