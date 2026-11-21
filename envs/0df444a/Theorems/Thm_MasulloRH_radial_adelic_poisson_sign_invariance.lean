-- Prove2me | Theorems.Thm_MasulloRH_radial_adelic_poisson_sign_invariance
-- name    : MasulloRH.radial_adelic_poisson_sign_invariance
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:06:12.00509+00:00
-- url     : https://prove2.me/theorems/8b98b7eb-9d95-46e9-a9c8-eb6a3108f4af
-- title:
--   The two finite-place sign conventions in rational adelic Poisson summation and their agreement on even tests
-- statement:
--   Let $u=(1,-1)$ on the rational adeles and $\chi(x)=\psi_{\mathbb Q}(ux)$, with $\psi_{\mathbb Q}$ the standard character trivial on diagonal rationals. The modified $\chi$ uses the same Fourier sign at the infinite and finite places as in the printed character. Its restriction to $\mathbb Q$ has kernel exactly $\tfrac12\mathbb Z$. For every adelic Schwartz–Bruhat test and any additive Haar measure $\mu$, the translated Poisson formula holds with $\chi$ and the reflected dual lattice $u\Delta\mathbb Q$, including the usual covolume factor. If $f(ux)=f(x)$, its entire Fourier transform is the same for both signs, and unshifted Poisson summation holds for $\chi$ on the ordinary diagonal. This includes tests invariant under the finite unit ideles.
-- source:
--   Masullo, Examples A.3.1.5–A.3.1.8 and Theorem 2.2.3.2. The opposite-sign issue at rational arguments was identified independently in F13 of the mccorvie/riemann-masullo errata, https://github.com/mccorvie/riemann-masullo/blob/main/ERRATA.md. The finite-sign-even sector and reflected-lattice formula are proved using the established adelic Poisson theorem 4340c7f0.

import Mathlib
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.StandardAddChar NumberField.AdelicFourier MeasureTheory
open scoped NumberField.AdeleRing
namespace MasulloRH

theorem radial_adelic_poisson_sign_invariance [MeasurableSpace 𝔸[ℚ]] [BorelSpace 𝔸[ℚ]]
    (μ : Measure 𝔸[ℚ]) [μ.IsAddHaarMeasure] (f : 𝔸[ℚ] → ℂ) (hf : f ∈ schwartzBruhat ℚ) :
    let u : 𝔸[ℚ] := (1,-1)
    let χ := psiQ.mulShift u
    (∀ q : ℚ, χ (algebraMap ℚ 𝔸[ℚ] q) = 1 ↔ ∃ k : ℤ, 2*q = k) ∧
    (∀ x : 𝔸[ℚ], (∑' q : ℚ, f (x + algebraMap ℚ 𝔸[ℚ] q)) =
       ((μ (AdelicBox.adelicBox ℚ)).toReal : ℂ)⁻¹ *
         ∑' q : ℚ, fourierIntegral χ μ f (u * algebraMap ℚ 𝔸[ℚ] q) *
           χ ((u * algebraMap ℚ 𝔸[ℚ] q)*x)) ∧
    ((∀ x : 𝔸[ℚ], f (u*x) = f x) →
       (∀ w : 𝔸[ℚ], fourierIntegral χ μ f w = fourierIntegral psiQ μ f w) ∧
       (∑' q : ℚ, f (algebraMap ℚ 𝔸[ℚ] q)) =
         ((μ (AdelicBox.adelicBox ℚ)).toReal : ℂ)⁻¹ *
           ∑' q : ℚ, fourierIntegral χ μ f (algebraMap ℚ 𝔸[ℚ] q)) := by sorry

end MasulloRH
