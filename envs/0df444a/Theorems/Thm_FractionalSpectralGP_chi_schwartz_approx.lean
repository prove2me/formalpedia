-- Prove2me | Theorems.Thm_FractionalSpectralGP_chi_schwartz_approx
-- name    : FractionalSpectralGP.chi_schwartz_approx
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:23:47.791029+00:00
-- url     : https://prove2.me/theorems/e2e8b8c5-f7e6-4271-a8e6-c34c0def50b7
-- title:
--   §5, p.16 — $\chi_t$ and $f_t=-i\chi_t$ are uniform limits of Fourier transforms of Schwartz functions
-- statement:
--   For every $t\in\mathbb R$:
--
--   1. the function $\chi_t(u)=\dfrac{e^{itu}-1}{u}$ (with $\chi_t(0)=it$) is a uniform limit on $\mathbb R$ of Fourier transforms $\widehat{s_n}$ of Schwartz functions $s_n$; and
--   2. so is $f_t(u)=\int_0^te^{iux}\,dx=-i\chi_t(u)$.
--
--   This places $1_{[0,t]}$ in the domain of the extended operator $Q_\sigma$ of Proposition 5.4, so that $X_\sigma(t)$ is well defined.
--
--   Differences from the source:
--   - encoding: approximation in the supremum norm by Schwartz functions → uniform convergence on ℝ of ŝ_n, s_n Schwartz; reason: the Fourier transform maps 𝒮 onto 𝒮, so the two classes of approximants coincide
--   - encoding: χ_t(u) = (e^{itu} − 1)/u → the same with the value it at u = 0; reason: the continuous extension; the printed quotient is 0/0 at 0
--   - generalization: χ_t → χ_t and f_t = −iχ_t; reason: the f_t clause follows from the χ_t clause by multiplying by −i; it is the form used to define X_σ
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §5, p.16 (proof of Proposition 5.4)

import Mathlib
import Definitions.Def_FractionalSpectralGP_paperFourier
import Definitions.Def_FractionalSpectralGP_ftInd
import Definitions.Def_FractionalSpectralGP_chiT

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- §5, p.16, in the proof of Proposition 5.4 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1): the function
`χ_t(u) = (e^{itu} − 1)/u` can be approximated in the supremum norm by (Fourier transforms of)
Schwartz functions; so can `f_t(u) = ∫₀ᵗ e^{iux} dx = −i χ_t(u)`.

**Formalization Note.** Uniform convergence on all of `ℝ`, for every real `t`. Since the Fourier
transform maps `𝒮` onto `𝒮`, approximation by `ŝ_n` is the page's approximation by Schwartz
functions. `χ_t(0) = it` is the continuous value. The `f_t` clause is the form used to define
`X_σ(t)`. -/
theorem chi_schwartz_approx (t : ℝ) :
    (∃ s : ℕ → 𝓢(ℝ, ℂ), TendstoUniformly (fun n => paperFourier (s n)) (chiT t) atTop) ∧
    ∃ s : ℕ → 𝓢(ℝ, ℂ), TendstoUniformly (fun n => paperFourier (s n)) (ftInd t) atTop := by sorry

end FractionalSpectralGP
