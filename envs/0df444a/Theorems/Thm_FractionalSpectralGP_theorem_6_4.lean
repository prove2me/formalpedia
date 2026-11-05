-- Prove2me | Theorems.Thm_FractionalSpectralGP_theorem_6_4
-- name    : FractionalSpectralGP.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:26:38.661103+00:00
-- url     : https://prove2.me/theorems/e1c8f0b0-fc25-436f-869d-39a4f1d6349e
-- title:
--   Theorem 6.4 — $W_\sigma$ is continuous in $\mathcal W$, stationary, and $E|W_\sigma(t)|^2\equiv1$
-- statement:
--   With the notation of the spectral setting, a real orthonormal basis $(h_n)$ and the white noise measure:
--
--   1. $t\mapsto W_\sigma(t)$ is continuous in the norm of $\mathcal W$;
--   2. $W_\sigma$ is stationary of second order: for all $t,s\in\mathbb R$,
--   $$
--   E\big[W_\sigma(t)\,\overline{W_\sigma(s)}\big]=\widehat\sigma(t-s);
--   $$
--   3. $W_\sigma$ has constant variance,
--   $$
--   E\big[|W_\sigma(t)|^2\big]\equiv1; \tag{6.5}
--   $$
--   4. if $\sigma$ is symmetric ($\sigma(-A)=\sigma(A)$), then each $W_\sigma(t)$ is real almost surely, and for all times $t_1,\dots,t_m$ and every shift $c$, the law of $(W_\sigma(t_1+c),\dots,W_\sigma(t_m+c))$ equals that of $(W_\sigma(t_1),\dots,W_\sigma(t_m))$.
--
--   $W_\sigma$ is thus a stationary (generalized-noise) process with spectral measure $\sigma$; its continuity is what STEP 2 of Theorem 7.1 uses.
--
--   Differences from the source:
--   - generalization: σ in the paper's class (orthonormal basis e^{iλ_n u}, λ_n ∈ πℕ₀, the measures σ_m) → any spectral setting: finite σ on [−1/2, 1/2], (e_{λ_n}) an orthonormal basis, λ_0 = 0; reason: no proof uses λ_n ∈ πℕ₀; the paper's measures are spectral settings
--   - generalization: h_n the Hermite functions → any real-valued orthonormal basis (h_n) of L²(ℝ, dx); reason: the proofs use only that (h_n) is a real orthonormal basis; the Hermite functions are one
--   - generalization: real Schwartz space and real white noise space → complex-valued Schwartz functions, L²(ℝ; ℂ), L²(P; ℂ) and complex chaos coefficients; reason: restricting to real functions gives the page's statement
--   - encoding: P from the Bochner–Minlos theorem, f ↦ f̃ the extension of (4.2) → P and ι parameters satisfying (4.1) and (4.2); reason: Minlos is not in Mathlib; (4.1) determines P and eq_4_2_isometry gives exactly one ι
--   - reading: W_σ stationary → second-order stationarity E[W(t) conj W(s)] = σ̂(t − s) for every σ, and strict stationarity of the finite-dimensional laws, with W real, when σ is symmetric; reason: the paper's 𝒲 is real, which happens for symmetric σ (such as σ_m), and its proof appeals to Gaussianity; for non-symmetric σ, W_σ is complex and its covariance is what is stationary
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Theorem 6.4, p.23

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_sigmaHat
import Definitions.Def_FractionalSpectralGP_IsRealHilbertBasis
import Definitions.Def_FractionalSpectralGP_Omega
import Definitions.Def_FractionalSpectralGP_IsWhiteNoise
import Definitions.Def_FractionalSpectralGP_IsWienerIsometry
import Definitions.Def_FractionalSpectralGP_Wsigma

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Theorem 6.4 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.23): the derivative process `W_σ` is continuous in the
`‖·‖_𝒲` norm; it is stationary and of constant variance, `E[|W_σ(t)|²] ≡ 1` (6.5).

**Formalization Note.** Four clauses: continuity of `t ↦ W_σ(t)` in `L²(P)`; the covariance
`E[W_σ(t) \overline{W_σ(s)}] = σ̂(t − s)` depends only on `t − s` (second-order stationarity, the
covariance of p.5); (6.5); and, when `σ` is symmetric (so `σ̂` is real and the paper's `𝒲` is
real), `W_σ(t)` is real a.e. and its finite-dimensional laws are invariant under time shifts
(strict stationarity of the Gaussian process). -/
theorem theorem_6_4 (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (hh : IsRealHilbertBasis h) (P : Measure Omega) (hP : IsWhiteNoise P)
    (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) (hι : IsWienerIsometry P ι) :
    Continuous (Wsigma S h P ι) ∧
    (∀ t s : ℝ, ∫ ω, (Wsigma S h P ι t : Omega → ℂ) ω *
        starRingEnd ℂ ((Wsigma S h P ι s : Omega → ℂ) ω) ∂P = sigmaHat S.σ (t - s)) ∧
    (∀ t : ℝ, ∫ ω, ‖(Wsigma S h P ι t : Omega → ℂ) ω‖ ^ 2 ∂P = 1) ∧
    (S.σ.map (fun u => -u) = S.σ →
      (∀ t : ℝ, ∀ᵐ ω ∂P, ((Wsigma S h P ι t : Omega → ℂ) ω).im = 0) ∧
      ∀ (m : ℕ) (τ : Fin m → ℝ) (c : ℝ),
        P.map (fun ω i => ((Wsigma S h P ι (τ i + c) : Omega → ℂ) ω).re) =
          P.map (fun ω i => ((Wsigma S h P ι (τ i) : Omega → ℂ) ω).re)) := by sorry

end FractionalSpectralGP
