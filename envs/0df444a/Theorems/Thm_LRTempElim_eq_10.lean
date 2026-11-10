-- Prove2me | Theorems.Thm_LRTempElim_eq_10
-- name    : LRTempElim.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:26:30.272329+00:00
-- url     : https://prove2.me/theorems/74afea7d-f001-49ef-9f13-2127e22457d6
-- title:
--   Eq. (10): the leading mean-risk coefficient $C=\operatorname{tr}(\Sigma V)$ from the local CLT and uniform integrability
-- statement:
--   Let $\nu$ be a probability law on $\mathbb R$, $\phi:\mathbb R\to\mathbb R^k$ a feature map with coordinates in $L^2(\nu)$, $\Sigma=\mathbb E_\nu[\phi\phi^\top]$, and $\ell^\star$ a target with $\ell^\star=\phi^\top\theta_*$ $\nu$-almost everywhere. Let $V$ be a covariance matrix (positive semidefinite). Let $\hat\theta_n:\Omega\to\mathbb R^k$ be estimators on a probability space $(\Omega,P)$ such that $\sqrt n(\hat\theta_n-\theta_*)$ converges in distribution to $N(0,V)$, and such that the squared scaled parameter errors $n\|\hat\theta_n-\theta_*\|^2$ are uniformly integrable. Then, with $C=\operatorname{tr}(\Sigma V)$,
--   $$
--   \mathbb E_{\mathrm{train}}\|f_{\hat\theta_n}-\ell^\star\|^2_{L^2(\nu)}=\frac Cn+o(n^{-1}),
--   $$
--   i.e. $n\,\mathbb E_P\big[\|\phi^\top\hat\theta_n-\ell^\star\|^2_{L^2(\nu)}\big]\to\operatorname{tr}(\Sigma V)$.
--
--   This converts the limiting covariance of an estimator into its first-order function risk; the goal theorem applies it to both estimators at $\nu=\nu_a$.
--
--   **Formalization Note** $\|\cdot\|$ is the Euclidean norm; uniform integrability is Mathlib's `UniformIntegrable` with exponent $1$.
--
--   Differences from the source:
--   - generalization: ν_a, ϕ = (1, x, x²) and ℓ⋆(x) = ax of §4.1 → any probability law ν on ℝ, any k and ϕ with coordinates in L²(ν), any ℓ⋆ with ℓ⋆ = ϕ⊤θ∗ ν-a.e.; reason: the Gaussian setting satisfies these hypotheses; the argument uses nothing else
--   - encoding: V_a the limiting covariance of √n(θ̂ − θ∗) → √n(θ̂_n − θ∗) converges in distribution to `multivariateGaussian 0 V` with V positive semidefinite; reason: a covariance is PSD; Mathlib's multivariateGaussian is a Dirac mass for non-PSD V
--   - encoding: the squared scaled parameter errors are uniformly integrable → `UniformIntegrable (fun n ω => n‖θ̂_n ω − θ∗‖²) 1 P`; reason: Mathlib's uniform integrability with p = 1 on a probability space
--   - encoding: = C(a)/n + o(n⁻¹) → n · E_P[risk] → tr(ΣV); reason: definition of o(n⁻¹)
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §4.1, eq. (10), p.7 (pdf p.9)

import Mathlib
import Definitions.Def_LRTempElim_Setting

open MeasureTheory ProbabilityTheory Matrix Filter Topology

namespace LRTempElim

/-- **Eq. (10)**: the leading mean-risk coefficient from the local CLT and uniform
integrability. Chen, Wu, Yang, Zeng, *Likelihood-Ratio Learning under Weak Overlap via Analytic
Temporal Elimination*, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee65139…), §4.1,
eq. (10), p.7 (pdf p.9).

"For the fixed-a limiting covariance `V_a` of `√n(θ̂ − θ∗)`, obtained through standard local
M-estimation and delta-method arguments [vdV98], write `C(a) = tr(Σ_{ν_a}V_a)`, where
`Σ_{ν_a} = E_{ν_a}[ϕϕ⊤]`. If the squared scaled parameter errors are uniformly integrable, this
coefficient gives `E_train‖f_θ̂ − ℓ⋆‖²_{L²(ν_a)} = C(a)/n + o(n⁻¹)`. (10)"

**Formalization Note.**
* Stated generically: any probability law `ν` on `ℝ`, any `k` and feature map `ϕ` with
  coordinates in `L²(ν)` (finite `Σ`), a target `ℓ⋆` with `ℓ⋆ = ϕ⊤θ∗` `ν`-a.e. (the calibrated
  target of §4.1), any probability space `(Ω, P)` and estimator sequence `θ̂_n : Ω → ℝᵏ`.
* "Limiting covariance `V` of `√n(θ̂ − θ∗)`": `√n(θ̂_n − θ∗)` converges in distribution to
  `multivariateGaussian 0 V` with `V` positive semidefinite (a covariance; Mathlib's
  `multivariateGaussian` is a Dirac mass otherwise).
* Uniform integrability of `n‖θ̂_n − θ∗‖²` (Euclidean norm) is `UniformIntegrable … 1 P`.
* `= C/n + o(n⁻¹)` is `n · E_P[‖ϕ⊤θ̂_n − ℓ⋆‖²_{L²(ν)}] → tr(ΣV)`. -/
theorem eq_10 {k : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν] (ϕ : ℝ → Fin k → ℝ)
    (hϕ : ∀ i, MemLp (fun x => ϕ x i) 2 ν) (ℓ : ℝ → ℝ) (θs : EuclideanSpace ℝ (Fin k))
    (hcal : ∀ᵐ x ∂ν, ℓ x = ϕ x ⬝ᵥ WithLp.ofLp θs)
    (V : Matrix (Fin k) (Fin k) ℝ) (hV : V.PosSemidef)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (θhat : ℕ → Ω → EuclideanSpace ℝ (Fin k))
    (hCLT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (θhat n ω - θs)) atTop id
      (fun _ => P) (multivariateGaussian 0 V))
    (hUI : UniformIntegrable (fun (n : ℕ) ω => (n : ℝ) * ‖θhat n ω - θs‖ ^ 2) 1 P) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, (∫ x, (ϕ x ⬝ᵥ WithLp.ofLp (θhat n ω) - ℓ x) ^ 2 ∂ν) ∂P)
      atTop (𝓝 (Matrix.trace (secondMoment ϕ ν * V))) := by sorry

end LRTempElim
