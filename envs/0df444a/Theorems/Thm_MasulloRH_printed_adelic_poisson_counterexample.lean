-- Prove2me | Theorems.Thm_MasulloRH_printed_adelic_poisson_counterexample
-- name    : MasulloRH.printed_adelic_poisson_counterexample
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:30:00.812433+00:00
-- url     : https://prove2.me/theorems/ca6e6b6d-b405-4aac-be62-edbdaef17c8d
-- title:
--   A compactly supported rational adelic Schwartz–Bruhat test that violates the printed same-sign Poisson formula
-- statement:
--   Let u=(1,−1) on the rational adeles and let χ(x)=ψ_Q(ux), the Fourier character with the same local signs printed in Examples A.3.1.5–A.3.1.8. There is a compactly supported adelic Schwartz–Bruhat test f with nonnegative real part that vanishes at every diagonal rational point and equals 1 at uΔ(1/3). For every additive Haar measure the real part of the covolume-normalized sum of its χ-Fourier transform over the ordinary diagonal rational lattice is at least 1. Thus the geometric lattice sum is 0 and the printed unshifted Fourier sum cannot equal it. The witness works for every Haar normalization. The separately proved finite-sign-even Poisson result describes a sector where the same-sign convention does work.
-- source:
--   Masullo, The Music of the Primes, Theorem 2.2.3.2 at the identity idele, Remark 2.2.3.3, and the local convention in Examples A.3.1.5–A.3.1.8. The independent mccorvie/riemann-masullo project identified the sign issue in erratum F13, https://github.com/mccorvie/riemann-masullo/blob/main/ERRATA.md. This proof constructs a compactly supported adelic test separating the two rational lattices and quantifies the failure in the same normalization as 8b98b7eb.

import Mathlib
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.StandardAddChar NumberField.AdelicFourier MeasureTheory
open scoped NumberField.AdeleRing
namespace MasulloRH

theorem printed_adelic_poisson_counterexample [MeasurableSpace 𝔸[ℚ]] [BorelSpace 𝔸[ℚ]] :
    let u : 𝔸[ℚ] := (1,-1)
    let χ := psiQ.mulShift u
    ∃ f ∈ schwartzBruhat ℚ, HasCompactSupport f ∧
      f (u * algebraMap ℚ 𝔸[ℚ] (1/3)) = 1 ∧ (∀ x, 0 ≤ (f x).re) ∧
      (∀ r : ℚ, f (algebraMap ℚ 𝔸[ℚ] r) = 0) ∧
      ∀ (μ : Measure 𝔸[ℚ]) [μ.IsAddHaarMeasure],
        (1:ℝ) ≤ (((μ (AdelicBox.adelicBox ℚ)).toReal : ℂ)⁻¹ *
          ∑' r : ℚ, fourierIntegral χ μ f (algebraMap ℚ 𝔸[ℚ] r)).re := by sorry

end MasulloRH
