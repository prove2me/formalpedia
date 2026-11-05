-- Prove2me | Theorems.Thm_FractionalSpectralGP_theorem_7_1_step3
-- name    : FractionalSpectralGP.theorem_7_1_step3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:30:45.20302+00:00
-- url     : https://prove2.me/theorems/212974cc-5e0a-408f-9c5d-5746432861a4
-- title:
--   Theorem 7.1, STEP 3 — the Riemann error equals $\sum_k\int_{t_k}^{t_{k+1}}(Y(t)-Y(t_k))\diamond W_\sigma(t)\,dt$
-- statement:
--   Let $p\in\mathbb N$ with $p>1$, let $Y:[a,b]\to\mathcal H'_p$ be continuous, and let $\Delta:a=t_0<t_1<\dots<t_n=b$ be a partition of $[a,b]$. Then the Riemann sum $\sum_{k=0}^{n-1}Y(t_k)\diamond(X_\sigma(t_{k+1})-X_\sigma(t_k))$ lies in $\mathcal H'_p$, and in $\mathcal H'_p$
--
--   $$
--   \int_a^bY(t)\diamond W_\sigma(t)\,dt-\sum_{k=0}^{n-1}Y(t_k)\diamond\big(X_\sigma(t_{k+1})-X_\sigma(t_k)\big)=\sum_{k=0}^{n-1}\int_{t_k}^{t_{k+1}}\big(Y(t)-Y(t_k)\big)\diamond W_\sigma(t)\,dt .
--   $$
--
--   The right side is small when the mesh is small, by the uniform continuity of $Y$; this is the last step of Theorem 7.1.
--
--   Differences from the source:
--   - generalization: σ in the paper's class (orthonormal basis e^{iλ_n u}, λ_n ∈ πℕ₀, the measures σ_m) → any spectral setting: finite σ on [−1/2, 1/2], (e_{λ_n}) an orthonormal basis, λ_0 = 0; reason: no proof uses λ_n ∈ πℕ₀; the paper's measures are spectral settings
--   - generalization: h_n the Hermite functions → any real-valued orthonormal basis (h_n) of L²(ℝ, dx); reason: the proofs use only that (h_n) is a real orthonormal basis; the Hermite functions are one
--   - generalization: real Schwartz space and real white noise space → complex-valued Schwartz functions, L²(ℝ; ℂ), L²(P; ℂ) and complex chaos coefficients; reason: restricting to real functions gives the page's statement
--   - encoding: P from the Bochner–Minlos theorem, f ↦ f̃ the extension of (4.2) → P and ι parameters satisfying (4.1) and (4.2); reason: Minlos is not in Mathlib; (4.1) determines P and eq_4_2_isometry gives exactly one ι
--   - encoding: formal series Σ f_α H_α and the norm ‖·‖_k of H′_k → coefficient families ℓ → ℂ and the ℓ²-norm of (f_α (2ℕ)^{−kα/2}); reason: the defining isometry of H′_k; same objects
--   - reading: Q_σ 1_{[0,t]} for every real t → the extended Q_σ at f_t(u) = ∫₀ᵗ e^{iux} dx (oriented integral); reason: (6.2) is stated for all t, so 1_{[0,t]} means −1_{[t,0]} for t < 0; f_t is the transform of the indicator, the printed χ_t differs by the factor i
--   - reading: p as in STEP 2 → hypotheses 1 < p, Y(t) ∈ H′_p for t ∈ [a, b] and Y continuous into H′_p; reason: STEP 1's conclusion and STEP 2's restriction
--   - encoding: ∫ in H′_p; partition a = t₀ < ⋯ < t_n = b → Bochner integrals of H′_p-valued maps (through the isometry of H′_p onto ℓ²); strictly increasing τ : Fin (n + 1) → ℝ with τ 0 = a, τ n = b; reason: the Riemann integral of a continuous Hilbert-space-valued function is its Bochner integral
--   - reading: the identity in H′_p → also asserts that the Riemann sum lies in H′_p; reason: implicit in the page; excludes a junk value
--   - encoding: the interval [a, b] with partitions a = t₀ < ⋯ < t_n = b → hypothesis a < b; reason: a partition with t₀ < t_n exists only when a < b; the degenerate a = b has no partitions
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Theorem 7.1, STEP 3, p.25

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_IsRealHilbertBasis
import Definitions.Def_FractionalSpectralGP_Omega
import Definitions.Def_FractionalSpectralGP_IsWhiteNoise
import Definitions.Def_FractionalSpectralGP_IsWienerIsometry
import Definitions.Def_FractionalSpectralGP_chaosCoeff
import Definitions.Def_FractionalSpectralGP_MemHprime
import Definitions.Def_FractionalSpectralGP_embedHprime
import Definitions.Def_FractionalSpectralGP_wick
import Definitions.Def_FractionalSpectralGP_Xsigma
import Definitions.Def_FractionalSpectralGP_Wsigma

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Theorem 7.1, STEP 3 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.25): for `p` as in STEP 2 and every partition
`Δ : a = t₀ < t₁ < ⋯ < t_n = b`,
`∫_a^b Y(t) ♦ W_σ(t) dt − Σ_{k=0}^{n−1} Y(t_k) ♦ (X_σ(t_{k+1}) − X_σ(t_k)) =
Σ_{k=0}^{n−1} ∫_{t_k}^{t_{k+1}} (Y(t) − Y(t_k)) ♦ W_σ(t) dt` in `𝓗'_p`.

**Formalization Note.** The Riemann sum is asserted to lie in `𝓗'_p`; all integrals are Bochner
integrals of `𝓗'_p`-valued functions (through the isometry `embedHprime p`); the partition is a
strictly increasing `τ : Fin (n + 1) → ℝ` with `τ 0 = a`, `τ n = b`. -/
theorem theorem_7_1_step3 (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (hh : IsRealHilbertBasis h) (P : Measure Omega) (hP : IsWhiteNoise P)
    (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) (hι : IsWienerIsometry P ι) (p : ℕ) (hp : 1 < p) (a b : ℝ) (hab : a < b)
    (Y : ℝ → (ℕ →₀ ℕ) → ℂ) (hY : ∀ t ∈ Set.Icc a b, MemHprime p (Y t))
    (hYc : ContinuousOn (fun t => embedHprime p (Y t)) (Set.Icc a b))
    (n : ℕ) (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ) (hτ0 : τ 0 = a) (hτn : τ (Fin.last n) = b) :
    MemHprime p (∑ k : Fin n, wick (Y (τ k.castSucc))
        (chaosCoeff P ι h (Xsigma S h P ι (τ k.succ) - Xsigma S h P ι (τ k.castSucc)))) ∧
    (∫ t in a..b, embedHprime p (wick (Y t) (chaosCoeff P ι h (Wsigma S h P ι t)))) -
        embedHprime p (∑ k : Fin n, wick (Y (τ k.castSucc))
          (chaosCoeff P ι h (Xsigma S h P ι (τ k.succ) - Xsigma S h P ι (τ k.castSucc)))) =
      ∑ k : Fin n, ∫ t in (τ k.castSucc)..(τ k.succ),
        embedHprime p (wick (Y t - Y (τ k.castSucc)) (chaosCoeff P ι h (Wsigma S h P ι t))) := by sorry

end FractionalSpectralGP
