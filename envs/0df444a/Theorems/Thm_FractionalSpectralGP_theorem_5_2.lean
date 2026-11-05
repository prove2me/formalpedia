-- Prove2me | Theorems.Thm_FractionalSpectralGP_theorem_5_2
-- name    : FractionalSpectralGP.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:28:21.217228+00:00
-- url     : https://prove2.me/theorems/63a16d57-cde9-4898-9755-f869b30e3edc
-- title:
--   Theorem 5.2 — $\|Q_\sigma\psi\|^2=\int|\widehat\psi|^2d\sigma$, continuity of $Q_\sigma$, and the bound (5.4)
-- statement:
--   Let $(\sigma,(\lambda_n))$ be a spectral setting and $(h_n)$ an orthonormal basis of $L^2(\mathbb R,dx)$. Then
--
--   1. for every Schwartz function $\psi$,
--   $$
--   \|Q_\sigma\psi\|^2_{L^2(\mathbb R,dx)}=\int_{\mathbb R}|\widehat\psi(u)|^2\,d\sigma(u); \tag{5.3}
--   $$
--   2. $Q_\sigma$ is continuous from $\mathcal S$ (with its Fréchet topology) into $L^2(\mathbb R,dx)$;
--   3. $K=\int_{\mathbb R}\frac{d\sigma(u)}{1+u^2}<\infty$; and
--   4. for every Schwartz function $\psi$,
--   $$
--   \|Q_\sigma\psi\|_{L^2(\mathbb R,dx)}\le\sqrt K\Big(\Big(\int_{\mathbb R}|\psi(x)|dx\Big)^2+\Big(\int_{\mathbb R}|\psi'(x)|dx\Big)^2\Big)^{1/2}. \tag{5.4}
--   $$
--
--   The isometry (5.3) is what allows $Q_\sigma$ to be extended by uniform approximation (Proposition 5.4).
--
--   Differences from the source:
--   - generalization: σ in the paper's class (orthonormal basis e^{iλ_n u}, λ_n ∈ πℕ₀, the measures σ_m) → any spectral setting: finite σ on [−1/2, 1/2], (e_{λ_n}) an orthonormal basis, λ_0 = 0; reason: no proof uses λ_n ∈ πℕ₀; the paper's measures are spectral settings
--   - generalization: h_n the Hermite functions → any orthonormal basis (h_n) of L²(ℝ, dx); reason: the proof uses only orthonormality and completeness
--   - generalization: ψ ∈ 𝒮 real-valued → ψ a complex-valued Schwartz function; reason: real ψ is a special case
--   - encoding: K < ∞ → 1/(1 + u²) is σ-integrable; reason: the meaning of a finite integral of a positive function
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Theorem 5.2, p.13

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_paperFourier
import Definitions.Def_FractionalSpectralGP_Qsigma

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Theorem 5.2 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.13): for a Schwartz function `ψ`,
`‖Q_σ ψ‖²_{L²(ℝ,dx)} = ∫_ℝ |ψ̂(u)|² dσ(u)` (5.3); `Q_σ` is a continuous operator from `𝒮` into
`L²(ℝ, dx)`; and `‖Q_σ ψ‖ ≤ √K ((∫|ψ|)² + (∫|ψ'|)²)^{1/2}` (5.4) with `K = ∫ dσ(u)/(1 + u²) < ∞`
(5.5).

**Formalization Note.** Continuity is for the Schwartz (Fréchet) topology of `𝓢(ℝ, ℂ)`. "`K < ∞`"
is the integrability of `1/(1 + u²)` against `σ`. -/
theorem theorem_5_2 (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
    (∀ ψ : 𝓢(ℝ, ℂ), ‖Qsigma S h ψ‖ ^ 2 = ∫ u, ‖paperFourier ψ u‖ ^ 2 ∂S.σ) ∧
    Continuous (Qsigma S h) ∧
    Integrable (fun u : ℝ => 1 / (1 + u ^ 2)) S.σ ∧
    ∀ ψ : 𝓢(ℝ, ℂ), ‖Qsigma S h ψ‖ ≤ Real.sqrt (∫ u, 1 / (1 + u ^ 2) ∂S.σ) *
      Real.sqrt ((∫ x, ‖ψ x‖) ^ 2 + (∫ x, ‖deriv ψ x‖) ^ 2) := by sorry

end FractionalSpectralGP
