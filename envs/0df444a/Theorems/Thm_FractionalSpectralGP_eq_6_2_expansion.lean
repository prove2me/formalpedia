-- Prove2me | Theorems.Thm_FractionalSpectralGP_eq_6_2_expansion
-- name    : FractionalSpectralGP.eq_6_2_expansion
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:30:52.74362+00:00
-- url     : https://prove2.me/theorems/e44f4792-0345-4ab6-b3f6-a88e82d89b28
-- title:
--   §6, (6.1)–(6.2) — the $Z_n$ are i.i.d. $N(0,1)$ and $X_\sigma(t)=\sum_n\big(\int_0^t\widehat\sigma(y-\lambda_n)dy\big)Z_n$
-- statement:
--   Let $(\sigma,(\lambda_n))$ be a spectral setting, $(h_n)$ a real orthonormal basis of $L^2(\mathbb R,dx)$, $P$ the white noise measure and $f\mapsto\widetilde f$ the isometry of (4.2). Put $Z_n=\widetilde{h_n}$. Then
--
--   1. each $Z_n$ is real-valued almost surely;
--   2. the $Z_n$ are independent;
--   3. each $Z_n$ has the standard normal law $N(0,1)$; and
--   4. for every $t\in\mathbb R$,
--   $$
--   X_\sigma(t)=\widetilde{Q_\sigma(1_{[0,t]})}=\sum_{n=0}^{\infty}\Big(\int_0^t\widehat\sigma(y-\lambda_n)\,dy\Big)Z_n, \tag{6.2}
--   $$
--   the series converging in $\mathcal W$.
--
--   The expansion (6.2) is the representation of $X_\sigma$ from which its increments and its derivative are computed.
--
--   Differences from the source:
--   - generalization: σ in the paper's class (orthonormal basis e^{iλ_n u}, λ_n ∈ πℕ₀, the measures σ_m) → any spectral setting: finite σ on [−1/2, 1/2], (e_{λ_n}) an orthonormal basis, λ_0 = 0; reason: no proof uses λ_n ∈ πℕ₀; the paper's measures are spectral settings
--   - generalization: h_n the Hermite functions → any real-valued orthonormal basis (h_n) of L²(ℝ, dx); reason: the proofs use only that (h_n) is a real orthonormal basis; the Hermite functions are one
--   - generalization: real Schwartz space and real white noise space → complex-valued Schwartz functions, L²(ℝ; ℂ), L²(P; ℂ) and complex chaos coefficients; reason: restricting to real functions gives the page's statement
--   - encoding: P from the Bochner–Minlos theorem, f ↦ f̃ the extension of (4.2) → P and ι parameters satisfying (4.1) and (4.2); reason: Minlos is not in Mathlib; (4.1) determines P and eq_4_2_isometry gives exactly one ι
--   - reading: Q_σ 1_{[0,t]} for every real t → the extended Q_σ at f_t(u) = ∫₀ᵗ e^{iux} dx (oriented integral); reason: (6.2) is stated for all t, so 1_{[0,t]} means −1_{[t,0]} for t < 0; f_t is the transform of the indicator, the printed χ_t differs by the factor i
--   - encoding: Z_n i.i.d. N(0, 1) → Z_n real a.e., the real parts mutually independent (iIndepFun), each with law gaussianReal 0 1; reason: the definition of an i.i.d. standard Gaussian sequence
--   - encoding: the series (6.2) in 𝒲 → HasSum in L²(P; ℂ); reason: same convergence
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §6, (6.1)–(6.2), p.21

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_sigmaHat
import Definitions.Def_FractionalSpectralGP_IsRealHilbertBasis
import Definitions.Def_FractionalSpectralGP_Omega
import Definitions.Def_FractionalSpectralGP_IsWhiteNoise
import Definitions.Def_FractionalSpectralGP_IsWienerIsometry
import Definitions.Def_FractionalSpectralGP_Zn
import Definitions.Def_FractionalSpectralGP_Xsigma

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- §6, (6.1)–(6.2) (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.21): the `Z_n = h̃_n` are independent, identically
distributed `N(0, 1)` random variables, and `X_σ(t) = Q̃_σ(1_{[0,t]}) = Σ_n (∫₀ᵗ σ̂(y − λ_n) dy) Z_n`.

**Formalization Note.** Each `Z_n` is real `P`-a.e.; their real parts are mutually independent with
law `N(0, 1)`; and the series (6.2) converges in `L²(P; ℂ)` for every real `t` (oriented integral). -/
theorem eq_6_2_expansion (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (hh : IsRealHilbertBasis h) (P : Measure Omega) (hP : IsWhiteNoise P)
    (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) (hι : IsWienerIsometry P ι) :
    (∀ n, ∀ᵐ ω ∂P, ((Zn P ι h n : Omega → ℂ) ω).im = 0) ∧
    iIndepFun (fun n ω => ((Zn P ι h n : Omega → ℂ) ω).re) P ∧
    (∀ n, P.map (fun ω => ((Zn P ι h n : Omega → ℂ) ω).re) = gaussianReal 0 1) ∧
    ∀ t : ℝ, HasSum (fun n => (∫ y in (0:ℝ)..t, sigmaHat S.σ (y - S.lam n)) • Zn P ι h n)
      (Xsigma S h P ι t) := by sorry

end FractionalSpectralGP
