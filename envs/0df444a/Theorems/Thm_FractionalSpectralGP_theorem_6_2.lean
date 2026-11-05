-- Prove2me | Theorems.Thm_FractionalSpectralGP_theorem_6_2
-- name    : FractionalSpectralGP.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:31:04.766325+00:00
-- url     : https://prove2.me/theorems/de4ce85f-10a0-447d-88a1-5b7543e92d4a
-- title:
--   Theorem 6.2 — $\|X_\sigma(t)-X_\sigma(s)\|_{\mathcal W}\le|t-s|$ and $X_\sigma'=W_\sigma$ in $\mathcal W$
-- statement:
--   With the notation of the spectral setting, a real orthonormal basis $(h_n)$, the white noise measure and $Z_n=\widetilde{h_n}$:
--
--   1. for all $t,s\in\mathbb R$,
--   $$
--   \|X_\sigma(t)-X_\sigma(s)\|_{\mathcal W}\le|t-s|; \tag{6.3}
--   $$
--   2. for every $t$, the series $W_\sigma(t)=\sum_{n=0}^\infty\widehat\sigma(t-\lambda_n)Z_n$ converges in $\mathcal W$; and
--   3. the map $t\mapsto X_\sigma(t)$ is differentiable in $\mathcal W$ at every $t\in\mathbb R$, with derivative
--   $$
--   X_\sigma'(t)=W_\sigma(t)=\sum_{n=0}^{\infty}\widehat\sigma(t-\lambda_n)\,Z_n. \tag{6.4}
--   $$
--
--   So for singular spectral measures the derivative process exists in the white noise space itself, not only in a Kondratiev space; this is what the sharper form of Theorem 7.1 rests on.
--
--   Differences from the source:
--   - generalization: σ in the paper's class (orthonormal basis e^{iλ_n u}, λ_n ∈ πℕ₀, the measures σ_m) → any spectral setting: finite σ on [−1/2, 1/2], (e_{λ_n}) an orthonormal basis, λ_0 = 0; reason: no proof uses λ_n ∈ πℕ₀; the paper's measures are spectral settings
--   - generalization: h_n the Hermite functions → any real-valued orthonormal basis (h_n) of L²(ℝ, dx); reason: the proofs use only that (h_n) is a real orthonormal basis; the Hermite functions are one
--   - generalization: real Schwartz space and real white noise space → complex-valued Schwartz functions, L²(ℝ; ℂ), L²(P; ℂ) and complex chaos coefficients; reason: restricting to real functions gives the page's statement
--   - encoding: P from the Bochner–Minlos theorem, f ↦ f̃ the extension of (4.2) → P and ι parameters satisfying (4.1) and (4.2); reason: Minlos is not in Mathlib; (4.1) determines P and eq_4_2_isometry gives exactly one ι
--   - reading: Q_σ 1_{[0,t]} for every real t → the extended Q_σ at f_t(u) = ∫₀ᵗ e^{iux} dx (oriented integral); reason: (6.2) is stated for all t, so 1_{[0,t]} means −1_{[t,0]} for t < 0; f_t is the transform of the indicator, the printed χ_t differs by the factor i
--   - encoding: t ↦ X_σ(t) differentiable in 𝒲 with derivative W_σ(t) → HasDerivAt X_σ (W_σ t) t for every real t, in L²(P; ℂ); reason: the Fréchet derivative of a curve in a Banach space
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Theorem 6.2, pp.21–22

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_sigmaHat
import Definitions.Def_FractionalSpectralGP_IsRealHilbertBasis
import Definitions.Def_FractionalSpectralGP_Omega
import Definitions.Def_FractionalSpectralGP_IsWhiteNoise
import Definitions.Def_FractionalSpectralGP_IsWienerIsometry
import Definitions.Def_FractionalSpectralGP_Zn
import Definitions.Def_FractionalSpectralGP_Xsigma
import Definitions.Def_FractionalSpectralGP_Wsigma

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Theorem 6.2 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, pp.21–22): `‖X_σ(t) − X_σ(s)‖_𝒲 ≤ |t − s|` for `t, s ∈ ℝ` (6.3);
the function `t ↦ X_σ(t)` is differentiable in `𝒲`, with derivative
`W_σ(t) = Σ_n σ̂(t − λ_n) Z_n` (6.4).

**Formalization Note.** Three clauses: the Lipschitz bound; the convergence of the series (6.4) in
`L²(P; ℂ)` to `W_σ(t)`; and `HasDerivAt X_σ (W_σ t) t` for every real `t`. -/
theorem theorem_6_2 (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (hh : IsRealHilbertBasis h) (P : Measure Omega) (hP : IsWhiteNoise P)
    (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) (hι : IsWienerIsometry P ι) :
    (∀ t s : ℝ, ‖Xsigma S h P ι t - Xsigma S h P ι s‖ ≤ |t - s|) ∧
    (∀ t : ℝ, HasSum (fun n => sigmaHat S.σ (t - S.lam n) • Zn P ι h n) (Wsigma S h P ι t)) ∧
    ∀ t : ℝ, HasDerivAt (Xsigma S h P ι) (Wsigma S h P ι t) t := by sorry

end FractionalSpectralGP
