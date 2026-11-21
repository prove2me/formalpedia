-- Prove2me | Theorems.Thm_MasulloAudit_rational_tate_one_line_nonintegrable
-- name    : MasulloAudit.rational_tate_one_line_nonintegrable
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:41:25.430443+00:00
-- url     : https://prove2.me/theorems/244e7082-b042-4bc7-9c62-49ed3f337cfa
-- title:
--   A Schwartz–Bruhat test on the rational adeles whose Tate integrand is not in L¹ anywhere on the one-line
-- statement:
--   For every multiplicative Haar measure on the full rational idele group, there is a Schwartz–Bruhat function f on the rational adeles with f(1)=1 for which x↦f(x)|x|^s is not Lebesgue integrable at any s with Re(s)=1. Here |x| is the actual idele norm and the integral is over the actual unit group of the rational adele ring. The same test works for all imaginary parts. In particular, every nonzero t gives a counterexample to the finiteness assertion in Proposition 3.4.2.1, with w=1+it and 0<A≤|t|. Ordinary norm-ordered Euler products can still give values of the meromorphic continuation there.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Proposition 3.4.2.1 and (3.4.2.1), pp. 144–145, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . Compare the ordered Euler products of Corollary B.7.2.5 and the separate finite-subset-net audit at https://prove2.me/theorems/8d932df9-1e3a-44d9-80a1-543238d799f5 .

import Definitions.Def_NumberField_TateGlobalZeta

open NumberField MeasureTheory

theorem MasulloAudit.rational_tate_one_line_nonintegrable [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ] [BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ]
    (ν : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [ν.IsHaarMeasure] :
    ∃ f ∈ AdelicFourier.schwartzBruhat ℚ, f 1=1 ∧
      ∀ s : ℂ, s.re=1 → ¬Integrable (fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        f x * ((TateGlobal.ideleNorm ℚ x : ℝ):ℂ)^s) ν := by sorry
