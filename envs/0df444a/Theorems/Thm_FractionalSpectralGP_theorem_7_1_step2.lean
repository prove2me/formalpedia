-- Prove2me | Theorems.Thm_FractionalSpectralGP_theorem_7_1_step2
-- name    : FractionalSpectralGP.theorem_7_1_step2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:27:03.232765+00:00
-- url     : https://prove2.me/theorems/a88f3ce7-d1da-431e-be55-796d4b7197cc
-- title:
--   Theorem 7.1, STEP 2 — $t\mapsto Y(t)\diamond W_\sigma(t)$ is continuous into $\mathcal H'_p$
-- statement:
--   Let $p\in\mathbb N$ with $p>1$, and let $Y:[a,b]\to\mathcal H'_p$ be continuous. Then $Y(t)\diamond W_\sigma(t)\in\mathcal H'_p$ for every $t\in[a,b]$, and the function
--
--   $$
--   t\longmapsto Y(t)\diamond W_\sigma(t)
--   $$
--
--   is continuous from $[a,b]$ into $\mathcal H'_p$. Here $W_\sigma(t)\in\mathcal W$ is read as an element of $S_{-1}$ through its chaos coefficients.
--
--   Continuity makes $\int_a^bY(t)\diamond W_\sigma(t)\,dt$ a Riemann integral of a continuous Hilbert-space-valued function.
--
--   Differences from the source:
--   - generalization: σ in the paper's class (orthonormal basis e^{iλ_n u}, λ_n ∈ πℕ₀, the measures σ_m) → any spectral setting: finite σ on [−1/2, 1/2], (e_{λ_n}) an orthonormal basis, λ_0 = 0; reason: no proof uses λ_n ∈ πℕ₀; the paper's measures are spectral settings
--   - generalization: h_n the Hermite functions → any real-valued orthonormal basis (h_n) of L²(ℝ, dx); reason: the proofs use only that (h_n) is a real orthonormal basis; the Hermite functions are one
--   - generalization: real Schwartz space and real white noise space → complex-valued Schwartz functions, L²(ℝ; ℂ), L²(P; ℂ) and complex chaos coefficients; reason: restricting to real functions gives the page's statement
--   - encoding: P from the Bochner–Minlos theorem, f ↦ f̃ the extension of (4.2) → P and ι parameters satisfying (4.1) and (4.2); reason: Minlos is not in Mathlib; (4.1) determines P and eq_4_2_isometry gives exactly one ι
--   - encoding: formal series Σ f_α H_α and the norm ‖·‖_k of H′_k → coefficient families ℓ → ℂ and the ℓ²-norm of (f_α (2ℕ)^{−kα/2}); reason: the defining isometry of H′_k; same objects
--   - reading: STEP 2 under the setting of STEP 1, "for p > 1" → hypotheses 1 < p, Y(t) ∈ H′_p for t ∈ [a, b] and Y continuous into H′_p; reason: these are STEP 1's conclusion and the page's restriction p > 1
--   - reading: continuous over [a, b] → Y(t) ♦ W_σ(t) ∈ H′_p and continuity into H′_p; reason: the page's estimate is in the norm ‖·‖_p of H′_p
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Theorem 7.1, STEP 2, p.25

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
import Definitions.Def_FractionalSpectralGP_Wsigma

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Theorem 7.1, STEP 2 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.25): for `p > 1` and `Y` continuous from `[a, b]` into
`𝓗'_p`, the function `t ↦ Y(t) ♦ W_σ(t)` is `𝓗'_p`-valued and continuous over `[a, b]`.

**Formalization Note.** `W_σ(t) ∈ 𝒲` enters `S_{−1}` through its chaos coefficients. The page's
"for `p > 1`" with `p ∈ ℕ` is `1 < p`. -/
theorem theorem_7_1_step2 (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (hh : IsRealHilbertBasis h) (P : Measure Omega) (hP : IsWhiteNoise P)
    (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) (hι : IsWienerIsometry P ι) (p : ℕ) (hp : 1 < p) (a b : ℝ)
    (Y : ℝ → (ℕ →₀ ℕ) → ℂ) (hY : ∀ t ∈ Set.Icc a b, MemHprime p (Y t))
    (hYc : ContinuousOn (fun t => embedHprime p (Y t)) (Set.Icc a b)) :
    (∀ t ∈ Set.Icc a b, MemHprime p (wick (Y t) (chaosCoeff P ι h (Wsigma S h P ι t)))) ∧
    ContinuousOn (fun t => embedHprime p (wick (Y t) (chaosCoeff P ι h (Wsigma S h P ι t))))
      (Set.Icc a b) := by sorry

end FractionalSpectralGP
