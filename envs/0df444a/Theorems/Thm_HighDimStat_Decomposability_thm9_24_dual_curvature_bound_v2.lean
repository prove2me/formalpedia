-- Prove2me | Theorems.Thm_HighDimStat_Decomposability_thm9_24_dual_curvature_bound_v2
-- name    : HighDimStat.Decomposability.thm9_24_dual_curvature_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:00.086965+00:00
-- url     : https://prove2.me/theorems/0cd00617-e08a-4cb0-83a6-34a0e34eb2de
-- title:
--   A dual-norm error bound under $\Phi^*$-curvature (Theorem 9.24), for convex costs
-- statement:
--   **Theorem 9.24.** A companion bound to Theorem 9.19, controlling the *dual*-norm error
--   $\Phi^*(\hat\theta-\theta^*)$ directly, under an alternative curvature condition stated on the
--   gradient mapping rather than the Taylor-series error.
--
--   Let $\Omega$ be a finite-dimensional inner product space, $\Phi$ a norm on $\Omega$, and let the
--   cost $\mathcal L_n$ be **convex** and differentiable (the standing assumptions of Section 9.4).
--   Given a target parameter $\theta^*\in\mathcal M$, assume (A1$'$) the cost satisfies the
--   $\Phi^*$-curvature condition of Definition 9.22 with curvature $\kappa>0$, tolerance $\tau_n$
--   and radius $R$ — i.e. $\Phi^*(\nabla \mathcal L_n(\theta^*+\Delta)-\nabla \mathcal L_n(\theta^*)) \ge
--   \kappa\Phi^*(\Delta)-\tau_n\Phi(\Delta)$ for every $\Delta$ with $\Phi^*(\Delta)\le R$ — and
--   (A2) $\Phi$ is decomposable with respect to $(\mathcal M,\bar{\mathcal M})$, with
--   $\tau_n\Psi^2(\bar{\mathcal M}) < \kappa/32$. Let $\hat\theta$ be any optimal solution of the
--   M-estimator $\min_\theta \mathcal L_n(\theta)+\lambda_n\Phi(\theta)$ ($\lambda_n>0$), conditioned
--   on $\mathcal G(\lambda_n)=\{\Phi^*(\nabla\mathcal L_n(\theta^*))\le\lambda_n/2\}$ and on
--   $\{\Phi^*(\hat\theta-\theta^*)\le R\}$. Then
--
--   $$
--   \Phi^*(\hat\theta-\theta^*) \le \frac{3\lambda_n}{\kappa}.
--   $$
--
--   **Formalization Note.** The retired version (`thm9_24_dual_curvature_bound`) omitted the
--   convexity of $\mathcal L_n$, a standing assumption of Section 9.4 (p. 277, footnote 2;
--   Proposition 9.13); the proof's first step — the inclusion of the error $\hat\Delta$ in the cone
--   $\mathbb C_{\theta^*}(\mathcal M,\bar{\mathcal M})$ — needs $\mathcal E_n(\hat\Delta)\ge 0$, i.e.
--   convexity, and the accepted disproof uses a double-well cost. The new statement adds
--   `hconv : ConvexOn ℝ Set.univ Ln` and changes nothing else. As before, the gradient increment
--   $\nabla\mathcal L_n(\theta^*+\Delta)-\nabla\mathcal L_n(\theta^*)$ is represented by a function
--   `Dg` tied to the actual gradient of `Ln` at every point by `hDg` (so differentiability
--   everywhere is part of the hypotheses); $\kappa>0$ and $\lambda_n>0$ are the chapter's
--   conventions; $\Psi(\bar{\mathcal M})$ is a bounded supremum in finite dimension, and for
--   $\bar{\mathcal M}=\{0\}$ it is Lean's $\sup\emptyset=0$, in which case the cone condition forces
--   $\hat\theta=\theta^*$ and the conclusion holds.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 285 (PDF p. 305), Theorem 9.24, Eqs. (9.55), (9.58)

import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

/-- Theorem 9.24 (p. 285): given a target `θ* ∈ M`, for a **convex** and differentiable cost
`Ln` (the standing assumption of Section 9.4, used through the error-cone inclusion of
Proposition 9.13), under (A1') — the cost satisfies the `Φ*`-curvature condition with
curvature `κ`, tolerance `τn` and radius `R`, witnessed by the gradient-increment map
`Dg : Δ ↦ ∇Ln(θ*+Δ) - ∇Ln(θ*)` — and (A2) — `Φ` decomposable with respect to `(M, M̄)` —
suppose `τn Ψ(M̄)² < κ/32`. Conditioned on `G(λn) ∩ {Φ*(θ̂-θ*) ≤ R}`, any optimal solution `θ̂`
of the M-estimator satisfies `Φ*(θ̂ - θ*) ≤ 3λn/κ`.

Correction relative to the retired version: the section-wide convexity assumption
`hconv : ConvexOn ℝ Set.univ Ln` was missing; without it the cone-inclusion step
`Δ̂ ∈ C_{θ*}(M, M̄)` fails and a non-convex cost admits far-away global minimizers. -/
theorem thm9_24_dual_curvature_bound_v2
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (Dg : Ω → Ω)
    (lamN κ τn R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hθM : θstar ∈ M)
    (hconv : ConvexOn ℝ Set.univ Ln)
    (hgrad : HasGradientAt Ln g θstar)
    (hDg : ∀ Δ : Ω, HasGradientAt Ln (g + Dg Δ) (θstar + Δ))
    (hcurv : DualCurvature Dg Φ κ τn R)
    (hκ : 0 < κ) (hlam : 0 < lamN)
    (htol : τn * subspaceLip Φ Mbar ^ 2 < κ / 32)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (hR : dualNorm Φ (θhat - θstar) ≤ R) :
    dualNorm Φ (θhat - θstar) ≤ 3 * lamN / κ := by sorry

end HighDimStat.Decomposability
