-- Prove2me | Theorems.Thm_HighDimStat_Decomposability_cor9_20_special_case_v2
-- name    : HighDimStat.Decomposability.cor9_20_special_case_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:51.082839+00:00
-- url     : https://prove2.me/theorems/3d7104a1-a57b-4221-b0b4-0535e4c2942b
-- title:
--   Corollary 9.20 (truth in the model subspace), with corrected constants: $\|\hat\theta-\theta^*\|^2 \le 36\lambda_n^2\Psi^2(\bar{\mathcal M})/\kappa^2$
-- statement:
--   **Corollary 9.20 (corrected constants).** When the target parameter lies exactly in the
--   model subspace, Theorem 9.19's family of bounds collapses to a purely multiplicative
--   estimation-error bound.
--
--   Let $\Omega$ be a finite-dimensional inner product space, $\Phi$ a norm on $\Omega$ that is
--   decomposable with respect to a subspace pair $(\mathcal M,\bar{\mathcal M})$, and let the cost
--   $\mathcal L_n$ be convex and differentiable at $\theta^*$ with gradient $g=\nabla\mathcal L_n(\theta^*)$.
--   Assume the restricted strong convexity condition
--   $\mathcal E_n(\Delta)\ge \frac{\kappa}{2}\|\Delta\|^2-\tau_n^2\Phi^2(\Delta)$ for all
--   $\|\Delta\|\le R$ ($\kappa>0$, $R>0$), the good event $\Phi^*(g)\le\lambda_n/2$ with
--   $\lambda_n>0$, the tolerance condition $\tau_n^2\Psi^2(\bar{\mathcal M})\le\kappa/64$, the radius
--   condition $6\lambda_n\Psi(\bar{\mathcal M})/\kappa\le R$, and $\theta^*\in\mathcal M$. Then any
--   optimal solution $\hat\theta$ of the M-estimator
--   $\min_\theta \mathcal L_n(\theta)+\lambda_n\Phi(\theta)$ satisfies
--
--   $$
--   \Phi(\hat\theta-\theta^*) \le \frac{24\lambda_n}{\kappa}\Psi^2(\bar{\mathcal M}), \qquad
--   \|\hat\theta-\theta^*\|^2 \le \frac{36\lambda_n^2}{\kappa^2}\Psi^2(\bar{\mathcal M}),
--   $$
--
--   where $\Psi(\bar{\mathcal M}) = \sup_{u\in\bar{\mathcal M}\setminus\{0\}}\Phi(u)/\|u\|$ is the
--   subspace Lipschitz constant.
--
--   **Formalization Note.** The retired version (`cor9_20_special_case`) transcribed the printed
--   bounds $\Phi(\hat\theta-\theta^*)\le 6\lambda_n\Psi^2/\kappa$ and
--   $\|\hat\theta-\theta^*\|^2\le 9\lambda_n^2\Psi^2/\kappa^2$ under the printed hypotheses
--   (including the radius condition $\sqrt{\varepsilon_n^2} = 3\lambda_n\Psi/\kappa\le R$), and the
--   accepted disproof exhibits a one-dimensional convex instance meeting every printed hypothesis
--   (with $\tau_n^2\Psi^2=\kappa/64$ exactly) and $\|\hat\theta-\theta^*\|^2 = 9.3025>9$; an
--   independent transcription of Theorem 9.19/Corollary 9.20 (reading-group notes on the book)
--   confirms the printed hypotheses and constants, so this is a correction to the **printed
--   source**, not to the transcription. The printed constant $9$ corresponds to curvature
--   $\kappa/2$, i.e. to $\tau_n=0$. With a positive tolerance, the RSC inequality combined with the
--   cone condition $\Phi(\Delta)\le 4\Psi(\bar{\mathcal M})\|\Delta\|$ leaves curvature
--   $\kappa/2-16\tau_n^2\Psi^2\ge\kappa/4$, and the book's proof route gives
--   $F(\Delta)\ge\frac{\kappa}{4}\|\Delta\|^2-\frac32\lambda_n\Psi\|\Delta\|>0$ for
--   $\|\Delta\|>6\lambda_n\Psi/\kappa$ (strictly, by a finer case analysis on
--   $\Phi(\Delta_{\bar{\mathcal M}^\perp})$), whence $\|\hat\theta-\theta^*\|\le 6\lambda_n\Psi/\kappa$
--   and $\Phi(\hat\theta-\theta^*)\le 4\Psi\|\hat\theta-\theta^*\|\le 24\lambda_n\Psi^2/\kappa$; this
--   requires the RSC ball to contain the corrected radius, hence the hypothesis
--   $6\lambda_n\Psi/\kappa\le R$ in place of $3\lambda_n\Psi/\kappa\le R$ (with only the printed
--   radius the conclusion can fail, since RSC says nothing outside $B(R)$). All other hypotheses
--   are the printed ones; the tolerance condition $\kappa/64$ suffices in this special case (the
--   general Theorem 9.19 needs $\kappa/128$ by the same argument). Convexity and differentiability
--   of $\mathcal L_n$ are the chapter's standing assumptions. $\Psi(\bar{\mathcal M})$ is a bounded
--   supremum in finite dimension; for $\bar{\mathcal M} = \{0\}$ it is Lean's $\sup\emptyset = 0$,
--   for which the statement is true ($\hat\theta=\theta^*$ from the cone condition).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 281 (PDF p. 301), Corollary 9.20, Eqs. (9.49a)-(9.49b) — corrected constants (24, 36 in place of the printed 6, 9) and radius condition 6λ_nΨ(M̄)/κ ≤ R; the printed bound is false for positive tolerance τ_n² (accepted disproof)

import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

/-- Corollary 9.20 (p. 281), **with corrected constants**: in addition to the conditions of
Theorem 9.19 (`Φ` a decomposable norm, `Ln` convex and differentiable at `θ*`, RSC with
curvature `κ`, tolerance `τn²` and radius `R`, the good event `G(λn)`, the tolerance condition
`τn² Ψ(M̄)² ≤ κ/64`, and a radius large enough to contain the error bound), suppose the target
`θ*` belongs to the model subspace `M`. Then any optimal solution `θ̂` of the M-estimator
satisfies `Φ(θ̂ - θ*) ≤ 24 λn/κ · Ψ(M̄)²` and `‖θ̂ - θ*‖² ≤ 36 λn²/κ² · Ψ(M̄)²`.

Correction to the printed source: the printed bounds `Φ(θ̂ - θ*) ≤ 6λn Ψ²/κ` and
`‖θ̂ - θ*‖² ≤ 9λn² Ψ²/κ²` (with radius condition `3λnΨ/κ ≤ R`) are false under the printed
hypotheses — a one-dimensional convex instance with `τn² Ψ² = κ/64` exactly has
`‖θ̂ - θ*‖² = 9.3025 > 9`. The printed `9` corresponds to curvature `κ/2`, i.e. to `τn = 0`;
with a positive tolerance the RSC inequality, combined with the cone condition
`Φ(Δ) ≤ 4Ψ(M̄)‖Δ‖`, only leaves curvature `κ/2 − 16τn²Ψ² ≥ κ/4`, and the book's own proof
route (`F(Δ) ≥ (κ/4)‖Δ‖² − (3/2)λnΨ‖Δ‖ > 0` for `‖Δ‖ > 6λnΨ/κ`) gives
`‖θ̂ - θ*‖ ≤ 6λnΨ(M̄)/κ`, hence `Φ(θ̂ - θ*) ≤ 4Ψ‖θ̂ - θ*‖ ≤ 24λnΨ²/κ`, provided the RSC ball
contains the corrected radius `6λnΨ/κ ≤ R`. -/
theorem cor9_20_special_case_v2
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN κ τnSq R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hRSC : RSC Ln g θstar Φ κ τnSq R)
    (hκ : 0 < κ) (hR : 0 < R) (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (htol : τnSq * subspaceLip Φ Mbar ^ 2 ≤ κ / 64)
    (hRbound : 6 * lamN / κ * subspaceLip Φ Mbar ≤ R)
    (hθM : θstar ∈ M) :
    Φ (θhat - θstar) ≤ 24 * lamN / κ * subspaceLip Φ Mbar ^ 2 ∧
      ‖θhat - θstar‖ ^ 2 ≤ 36 * lamN ^ 2 / κ ^ 2 * subspaceLip Φ Mbar ^ 2 := by sorry

end HighDimStat.Decomposability
