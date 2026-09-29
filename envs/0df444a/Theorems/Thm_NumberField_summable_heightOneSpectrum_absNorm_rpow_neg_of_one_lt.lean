-- Prove2me | Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
-- name    : NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/e8495fdf-032f-5485-9d21-d09f772c913f
-- title:
--   Summability of (N𝔭)^{-σ} over primes for σ>1
-- statement:
--   Let $F$ be a number field (a field of characteristic zero, finite-dimensional over $\mathbb{Q}$, with ring of integers $\mathcal{O}_F$ denoted $\mathcal{O} F$), and let $\sigma$ be a real number with $1 < \sigma$. The index set is the height-one spectrum of the Dedekind domain $\mathcal{O}_F$, that is, the type of non-zero prime ideals $v$ of $\mathcal{O}_F$, each carrying its underlying ideal `v.asIdeal`. The assertion is that the family of real numbers indexed by this type whose value at $v$ is $(\mathrm{N}(v.\mathrm{asIdeal}))^{-\sigma}$, where $\mathrm{N}$ is the absolute norm `Ideal.absNorm` (a natural number, cast to $\mathbb{R}$, and the power taken as a real `rpow`), is summable in $\mathbb{R}$ in the unconditional sense of `Summable`. Equivalently, the prime part of the Dirichlet series of the Dedekind zeta function of $F$ converges absolutely at every real argument $\sigma > 1$.
--
--   This is the convergence of the Euler product of the Dedekind zeta function of $F$ in the half-plane $\mathrm{Re}\,s > 1$, in its real, prime-by-prime form. It is used throughout the analytic part of the development, for instance in the estimates underlying the meromorphic continuation of completed $L$-functions and of Whittaker and intertwining integrals for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt.lean

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
    (F : Type) [Field F] [NumberField F] {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) := by sorry
