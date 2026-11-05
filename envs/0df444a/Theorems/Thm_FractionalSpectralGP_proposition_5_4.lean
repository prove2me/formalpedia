-- Prove2me | Theorems.Thm_FractionalSpectralGP_proposition_5_4
-- name    : FractionalSpectralGP.proposition_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:29:12.963448+00:00
-- url     : https://prove2.me/theorems/65d1a6fe-4924-4215-be26-d6e4c2291640
-- title:
--   Proposition 5.4 — extension of $Q_\sigma$: $Q_\sigma f=\lim Q_\sigma s_n$ when $|f-\widehat{s_n}|_\infty\to0$
-- statement:
--   Let $(\sigma,(\lambda_n))$ be a spectral setting and $(h_n)$ an orthonormal basis of $L^2(\mathbb R,dx)$. Let $f\in L^2(d\sigma)$ and let $(s_n)$ be Schwartz functions with
--
--   $$
--   \lim_{n\to\infty}|f-\widehat{s_n}|_\infty=0. \tag{5.8}
--   $$
--
--   Then $(Q_\sigma s_n)$ is a Cauchy sequence in $L^2(\mathbb R,dx)$, and it converges to $Q_\sigma f$, a limit that is the same for every sequence satisfying (5.8).
--
--   This extension is what defines $Q_\sigma1_{[0,t]}$ and hence the process $X_\sigma$.
--
--   Differences from the source:
--   - generalization: σ in the paper's class (orthonormal basis e^{iλ_n u}, λ_n ∈ πℕ₀, the measures σ_m) → any spectral setting: finite σ on [−1/2, 1/2], (e_{λ_n}) an orthonormal basis, λ_0 = 0; reason: no proof uses λ_n ∈ πℕ₀; the paper's measures are spectral settings
--   - generalization: h_n the Hermite functions → any orthonormal basis (h_n) of L²(ℝ, dx); reason: the proof uses only (5.3)
--   - generalization: Schwartz functions real-valued → complex-valued Schwartz functions; reason: real ones are a special case
--   - reading: |f − ŝ_n|_∞ for f ∈ L²(dσ) → the σ-essential supremum (eLpNorm ⊤ σ); reason: f is an element of L²(dσ); the essential supremum is at most the supremum over ℝ, so this hypothesis is the weaker one and the statement the stronger
--   - encoding: the limit is the same for all sequences satisfying (5.8), denoted Q_σ f → convergence to the single value QsigmaExt S h f; reason: a common limit for all sequences is exactly convergence to one fixed value
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Proposition 5.4, p.15

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_paperFourier
import Definitions.Def_FractionalSpectralGP_Qsigma
import Definitions.Def_FractionalSpectralGP_QsigmaExt

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Proposition 5.4 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.15): let `f ∈ L²(dσ)` be such that `|f − ŝ_n|_∞ → 0` for
some sequence `(s_n)` of Schwartz functions (5.8). Then `(Q_σ s_n)` is a Cauchy sequence in
`L²(ℝ, dx)`, and its limit is the same for all sequences satisfying (5.8); it is denoted `Q_σ f`.

**Formalization Note.** `|·|_∞` is the `σ`-essential supremum (`eLpNorm · ⊤ σ`), the norm in which
`f ∈ L²(dσ)` is a class; this is the strong reading (uniform convergence on `ℝ` implies it).
"The limit is the same for all sequences" is stated as convergence to the single value
`QsigmaExt S h f`, which therefore does not depend on the sequence. -/
theorem proposition_5_4 (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) (f : ℝ → ℂ)
    (hf : MemLp f 2 S.σ) (s : ℕ → 𝓢(ℝ, ℂ))
    (hs : Tendsto (fun n => eLpNorm (f - paperFourier (s n)) ⊤ S.σ) atTop (𝓝 0)) :
    CauchySeq (fun n => Qsigma S h (s n)) ∧
    Tendsto (fun n => Qsigma S h (s n)) atTop (𝓝 (QsigmaExt S h f)) := by sorry

end FractionalSpectralGP
