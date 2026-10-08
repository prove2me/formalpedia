-- Prove2me | Theorems.Thm_Helfgott_etaTwo_twisted_prime_LFunction_mellin
-- name    : Helfgott.etaTwo_twisted_prime_LFunction_mellin
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T09:05:24.141984+00:00
-- url     : https://prove2.me/theorems/c503b5d6-f83e-4e64-9195-16c3b7837ba4
-- title:
--   Complete logarithmic-smoothing prime sum as an absolutely convergent continued-L-function integral
-- statement:
--   Let $q>0$, let $\chi$ be a complex Dirichlet character modulo $q$, let $\sigma>1$, and let $x>0$. Use Helfgott's actual compact smoothing $\eta_2(u)=4\max(\log 2-|\log(2u)|,0)$ for $u>0$, and zero otherwise. Let $L(s,\chi)$ be the analytically continued Dirichlet L-function.
--
--   The full prime-power series is summable, the integral is absolutely convergent, and
--
--   $$\sum_{n\ge0}\chi(n)\Lambda(n)\eta_2(n/x)=\frac1{2\pi}\int_{-\infty}^{\infty}x^{\sigma+it}\frac{4(1-2^{-(\sigma+it)})^2}{(\sigma+it)^2}\left(-\frac{L'}L(\sigma+it,\chi)\right)\,dt.$$
--
--   Every smoothing and convergence fact is proved. In particular the complete Mellin transform is $4(1-2^{-s})^2/s^2$ for $s\ne0$, and for every $\sigma>0$ its vertical norm is at most $4(1+2^{-\sigma})^2/(\sigma^2+t^2)$. No smoothing regularity, zero information or prime-distribution estimate is assumed. This theorem treats the compact logarithmic smoothing without an additional additive phase; quantitative explicit-formula and Gaussian-smoothing estimates remain separate obligations.
-- source:
--   Helfgott, Major arcs for Goldbach’s problem, https://arxiv.org/abs/1305.2897, logarithmic smoothing and Mellin explicit-formula setup; coordinated smoothing in https://arxiv.org/html/1312.7748v2. Complete original smoothing-transform calculation included. Mathlib Mellin inversion: Lawrence Wu; Mellin transform and continued L-functions: David Loeffler and Michael Stoll; twisted von Mangoldt logarithmic derivative: Michael Stoll. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
open MeasureTheory Set

theorem Helfgott.etaTwo_twisted_prime_LFunction_mellin (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x : ℝ) (hσ : 1 < σ) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
      (x : ℂ) ^ s * (4 * (1 - (2 : ℂ) ^ (-s)) ^ 2 / s ^ 2) *
        (-deriv χ.LFunction s / χ.LFunction s)) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) *
      (Helfgott.etaTwo ((n : ℝ) / x) : ℂ))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
        (x : ℂ) ^ s * (4 * (1 - (2 : ℂ) ^ (-s)) ^ 2 / s ^ 2) *
          (-deriv χ.LFunction s / χ.LFunction s)) := by sorry
