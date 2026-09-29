-- Prove2me | Theorems.Thm_HighDimStat_Decomposability_thm9_24_dual_curvature_bound
-- name    : HighDimStat.Decomposability.thm9_24_dual_curvature_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:18:07.86898+00:00
-- url     : https://prove2.me/theorems/8ab6ee94-5b50-4aa3-a697-5a2f1a12552a
-- title:
--   A dual-norm error bound under Phi*-curvature (Theorem 9.24)
-- statement:
--   **Theorem 9.24.** A companion bound to Theorem 9.19, controlling the *dual*-norm error
--   $\Phi^*(\hat\theta-\theta^*)$ directly, under an alternative curvature condition stated on the
--   gradient mapping rather than the Taylor-series error.
--
--   Given a target parameter $\theta^*\in\mathcal M$, assume (A1$'$) the cost satisfies the
--   $\Phi^*$-curvature condition of Definition 9.22 with curvature $\kappa>0$, tolerance $\tau_n$
--   and radius $R$ — i.e. $\Phi^*(\nabla L_n(\theta^*+\Delta)-\nabla L_n(\theta^*)) \ge
--   \kappa\Phi^*(\Delta)-\tau_n\Phi(\Delta)$ for every $\Delta$ with $\Phi^*(\Delta)\le R$ — and
--   (A2) $\Phi$ is decomposable with respect to $(\mathcal M,\bar{\mathcal M})$, with
--   $\tau_n\Psi^2(\bar{\mathcal M}) < \kappa/32$. Let $\hat\theta$ be any optimal solution of the
--   M-estimator, conditioned on $\mathcal G(\lambda_n)\cap\{\Phi^*(\hat\theta-\theta^*)\le R\}$.
--   Then
--
--   $$
--   \Phi^*(\hat\theta-\theta^*) \le \frac{3\lambda_n}{\kappa}.
--   $$
--
--   Like Theorem 9.19, this claim is deterministic given the stated conditioning; the
--   conditioning event $\{\Phi^*(\hat\theta-\theta^*)\le R\}$ is a genuine second hypothesis
--   beyond $\mathcal G(\lambda_n)$ that must itself be certified (often via Theorem 9.19) before
--   this result can be applied, per the book's own remark.
--
--   **Formalization Note** The gradient increment $\nabla L_n(\theta^*+\Delta)-\nabla
--   L_n(\theta^*)$ is represented by an explicit function `Dg : Ω → Ω`, tied to `Ln`'s actual
--   gradient via `hDg : ∀ Δ, HasGradientAt Ln (g + Dg Δ) (θstar + Δ)` (so `g + Dg Δ` really is
--   $\nabla L_n(\theta^*+\Delta)$, with `g = ∇Ln(θstar)`). `hκ : 0 < κ` and `hlam : 0 < lamN`
--   make explicit the positivity conventions Definition 9.22 and the chapter's regularization
--   weight carry throughout (see `MODERATION_NOTES.md`).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 285 (PDF p. 305), Theorem 9.24, Eqs. (9.55), (9.58)

import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

/-- Theorem 9.24 (p. 285): given a target `θ* ∈ M`, under (A1') — the cost satisfies the
`Φ*`-curvature condition with curvature `κ`, tolerance `τn` and radius `R`, witnessed by the
gradient-increment map `Dg : Δ ↦ ∇Ln(θ*+Δ) - ∇Ln(θ*)` — and (A2) — `Φ` decomposable with
respect to `(M, M̄)` — suppose `τn Ψ(M̄)² < κ/32`. Conditioned on `G(λn) ∩ {Φ*(θ̂-θ*) ≤ R}`, any
optimal solution `θ̂` of the M-estimator satisfies `Φ*(θ̂ - θ*) ≤ 3λn/κ`. -/
theorem thm9_24_dual_curvature_bound
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (Dg : Ω → Ω)
    (lamN κ τn R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hθM : θstar ∈ M)
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
