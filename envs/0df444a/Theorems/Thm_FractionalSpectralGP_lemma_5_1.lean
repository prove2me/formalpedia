-- Prove2me | Theorems.Thm_FractionalSpectralGP_lemma_5_1
-- name    : FractionalSpectralGP.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:28:03.574038+00:00
-- url     : https://prove2.me/theorems/0a98b107-1a54-4d9a-83a3-cd6488598f79
-- title:
--   Lemma 5.1 — $Q_\sigma\psi=\sum_n\big(\int\widehat\sigma(y-\lambda_n)\psi(y)\,dy\big)h_n$ (5.2)
-- statement:
--   Let $(\sigma,(\lambda_n))$ be a spectral setting, $(h_n)$ an orthonormal basis of $L^2(\mathbb R,dx)$, and $\psi$ a Schwartz function. Then
--
--   $$
--   Q_\sigma\psi=\sum_{n=0}^{\infty}\Big(\int_{\mathbb R}\widehat\sigma(y-\lambda_n)\,\psi(y)\,dy\Big)h_n, \tag{5.2}
--   $$
--
--   the series converging in $L^2(\mathbb R,dx)$. Here $Q_\sigma\psi=\widehat\psi(T)h_0$ is defined by the functional calculus of $T=WM_uW^*$.
--
--   The expansion (5.2) converts the operator-theoretic definition of $Q_\sigma$ into explicit coefficients, which become those of $X_\sigma(t)$ in (6.2).
--
--   Differences from the source:
--   - generalization: σ in the paper's class (orthonormal basis e^{iλ_n u}, λ_n ∈ πℕ₀, the measures σ_m) → any spectral setting: finite σ on [−1/2, 1/2], (e_{λ_n}) an orthonormal basis, λ_0 = 0; reason: no proof uses λ_n ∈ πℕ₀; the paper's measures are spectral settings
--   - generalization: h_n the Hermite functions → any orthonormal basis (h_n) of L²(ℝ, dx); reason: the proof uses only orthonormality and completeness
--   - generalization: ψ ∈ 𝒮 real-valued → ψ a complex-valued Schwartz function; reason: real ψ is a special case
--   - encoding: (Q_σψ)(x) = Σ_n (…) h_n(x) → HasSum of the series in L²(ℝ, dx); reason: an identity of elements of L²(ℝ, dx)
--   - encoding: ψ̂(T) by the functional calculus → cfc of T applied to z ↦ ψ̂(Re z); reason: T is self-adjoint, so its spectrum is real and this is ψ̂(T)
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Lemma 5.1, p.12

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_sigmaHat
import Definitions.Def_FractionalSpectralGP_Qsigma

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Lemma 5.1 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.12): for a Schwartz function `ψ`,
`(Q_σ ψ)(x) = Σ_{n=0}^∞ (∫_ℝ σ̂(y − λ_n) ψ(y) dy) h_n(x)` (5.2), the series converging in
`L²(ℝ, dx)`.

**Formalization Note.** `Q_σ ψ = ψ̂(T) h₀` is defined by the functional calculus, not by (5.2).
`ψ` is complex-valued (generalizing the paper's real `𝒮`) and `(h_n)` is any orthonormal basis. -/
theorem lemma_5_1 (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) (ψ : 𝓢(ℝ, ℂ)) :
    HasSum (fun n => (∫ y, sigmaHat S.σ (y - S.lam n) * ψ y) • h n) (Qsigma S h ψ) := by sorry

end FractionalSpectralGP
