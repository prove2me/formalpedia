-- Prove2me | Theorems.Thm_Helfgott_twisted_prime_LFunction_mellin
-- name    : Helfgott.twisted_prime_LFunction_mellin
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T08:48:51.279994+00:00
-- url     : https://prove2.me/theorems/ed8e6df2-839c-448b-842f-a96c8fdab1b2
-- title:
--   Absolutely convergent Mellin representation of smoothed character prime sums by the continued L-function
-- statement:
--   Let $q>0$, let $\chi$ be a complex Dirichlet character modulo $q$, and let $\sigma>1$ and $x>0$. Let $f:(0,\infty)\to\mathbb C$ be continuous, Mellin-convergent on $\Re s=\sigma$, and have absolutely integrable Mellin transform along that vertical line. Write $F(s)=\int_0^\infty f(u)u^{s-1}\,du$ and let $L(s,\chi)$ denote the analytically continued Dirichlet L-function.
--
--   Then the integral below is absolutely convergent, the complete prime-power series is summable, and
--
--   $$\sum_{n\ge0}\chi(n)\Lambda(n)f(n/x)=\frac1{2\pi}\int_{-\infty}^{\infty}x^{\sigma+it}F(\sigma+it)\left(-\frac{L'}L(\sigma+it,\chi)\right)\,dt.$$
--
--   The proof includes the Mellin inversion at each positive integer, zero-index handling, convergence of the full twisted von Mangoldt Dirichlet series, every sum/integral interchange, and equality of the L-series and its derivative with the continued L-function on the convergence half-plane. The regularity assumptions on $f$ are explicit; this theorem does not assert that a particular smoothing satisfies them or shift the line through zeros.
-- source:
--   Classical Mellin-inversion starting identity for explicit formulas; applied in Helfgott, Major arcs for Goldbach’s problem, https://arxiv.org/abs/1305.2897. Mathlib Mellin inversion: Lawrence Wu; Mellin transform: David Loeffler; Dirichlet-series logarithmic derivative: Michael Stoll; continued Dirichlet L-functions: David Loeffler and Michael Stoll. Written by Codex.

import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory Set

theorem Helfgott.twisted_prime_LFunction_mellin (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x : ℝ) (hσ : 1 < σ) (hx : 0 < x)
    (f : ℝ → ℂ) (hf : MellinConvergent f (σ : ℂ))
    (hF : Complex.VerticalIntegrable (mellin f) σ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ))) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      (-deriv χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) /
        χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I))) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * f ((n : ℝ) / x))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (-deriv χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) /
          χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I))) := by sorry
