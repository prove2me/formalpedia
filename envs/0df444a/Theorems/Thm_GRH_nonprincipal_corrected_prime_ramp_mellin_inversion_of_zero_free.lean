-- Prove2me | Theorems.Thm_GRH_nonprincipal_corrected_prime_ramp_mellin_inversion_of_zero_free
-- name    : GRH.nonprincipal_corrected_prime_ramp_mellin_inversion_of_zero_free
-- status  : Proved
-- author  : @GeorgeCoote
-- created : 2026-11-21T17:25:57.409604+00:00
-- url     : https://prove2.me/theorems/d79e18ee-fc32-4c3c-bf2e-8f5561a90c14
-- title:
--   Mellin inversion for the corrected Dirichlet prime ramp on a zero-free line
-- statement:
--   Let $\chi$ be a nonprincipal Dirichlet character modulo $q\ge 1$. Suppose $L(s,\chi)$ has no zeros in $\operatorname{Re}s>\alpha$, where $0<\alpha<\sigma<1$. Write $D(s)=L'(s,\chi)/L(s,\chi)$ and $s_t=\sigma+it$. Then $t\mapsto-D(s_t)/(s_t(s_t-1))$ is integrable on $\mathbb R$, and for every real $y>1$,
--   $$
--   \sum_{1\le n\le y}\Lambda(n)\chi(n)(y/n-1)_+ + yD(1)
--   =\frac1{2\pi}\int_{\mathbb R}\frac{-D(s_t)}{s_t(s_t-1)}y^{s_t}\,dt.
--   $$
--
--   Here $x_+=\max(x,0)$. The identity and integrability allow any such vertical line to be used for a power bound on the corrected ramp.
-- source:
--   The corrected ramp kernel and the Perron inversion and residue at one are those in the verified proof of GRH.nonprincipal_corrected_prime_ramp_abs_le_of_zero_bound, https://prove2.me/theorems/5fd56414-b029-4410-9f5a-fdee501f34cd. The strict zero-free gap permits shifting to the prescribed line. For the disk estimate for the logarithmic derivative, see https://prove2.me/theorems/e46b601f-53e0-4046-97cf-3a2754f81257.

import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Finset ArithmeticFunction MeasureTheory

namespace GRH

theorem nonprincipal_corrected_prime_ramp_mellin_inversion_of_zero_free
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (α σ : ℝ) (hα : 0 < α) (hασ : α < σ) (hσ : σ < 1)
    (hZero : ∀ z : ℂ, α < z.re → χ.LFunction z ≠ 0) :
    let s (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    let F (t : ℝ) : ℂ := -logDeriv χ.LFunction (s t) / (s t * (s t - 1))
    Integrable F ∧ ∀ y : ℝ, 1 < y →
      (∑ n ∈ range (⌊y⌋₊ + 1), (vonMangoldt n : ℂ) * χ (n : ZMod q) *
        (max (y / (n : ℝ) - 1) 0 : ℝ)) +
        (y : ℂ) * (deriv χ.LFunction 1 / χ.LFunction 1) =
      (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, (y : ℂ) ^ s t * F t := by
  sorry

end GRH
