-- Prove2me | Theorems.Thm_MasulloRH_principal_idele_iff_unshifted_poisson
-- name    : MasulloRH.principal_idele_iff_unshifted_poisson
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T04:10:33.512467+00:00
-- url     : https://prove2.me/theorems/371f338e-0bd9-43d0-aa60-0239ec561cb2
-- title:
--   The unshifted rational adelic Poisson formula classifies principal idèle twists
-- statement:
--   For an arbitrary rational idèle c, let χ_c(x)=ψ_Q(cx). The covolume-normalized Poisson formula on the ordinary diagonal lattice with the same unshifted lattice of frequencies holds for every Schwartz–Bruhat test iff c is a principal idèle. If c is nonprincipal, a single compactly supported test with nonnegative real part vanishes on every rational yet has normalized Fourier sum at least the idèle norm of c⁻¹ in real part, for every Haar measure. For every physical idèle a, character twist c, translation x and test f, the corrected frequency lattice is (ac)⁻¹ Q and the normalized prefactor is the reciprocal of the idèle norm of a times the reciprocal covolume.
-- source:
--   General classification extending the proved Masullo sign counterexample ca6e6b6d and even-test formula 8b98b7eb, in the normalization of manuscript Theorem 2.2.3.2 / Remark 2.2.3.3. The printed sign problem was recorded in the independent formalization’s erratum F13 (https://github.com/mccorvie/riemann-masullo/blob/main/ERRATA.md). The proof uses the global character annihilator 20073258, Fourier scaling f7b55f44 and translated Poisson summation for the canonical ψ_Q.

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.StandardAddChar NumberField.AdelicFourier MeasureTheory
open scoped NumberField.AdeleRing
namespace MasulloRH

theorem principal_idele_iff_unshifted_poisson [MeasurableSpace 𝔸[ℚ]] [BorelSpace 𝔸[ℚ]]
    (c : 𝔸[ℚ]ˣ) (μ : Measure 𝔸[ℚ]) [μ.IsAddHaarMeasure] :
    let D := algebraMap ℚ 𝔸[ℚ]
    let χ := psiQ.mulShift (c:𝔸[ℚ])
    let V (ν : Measure 𝔸[ℚ]) := ((ν (AdelicBox.adelicBox ℚ)).toReal : ℂ)⁻¹
    ((c:𝔸[ℚ]) ∈ Set.range D ↔ ∀ f ∈ schwartzBruhat ℚ,
      (∑' q : ℚ,f (D q)) = V μ*(∑' q : ℚ,fourierIntegral χ μ f (D q))) ∧
    ((c:𝔸[ℚ]) ∉ Set.range D →
      ∃ f ∈ schwartzBruhat ℚ, HasCompactSupport f ∧ (∀ x,0 ≤ (f x).re) ∧
        (∀ q : ℚ,f (D q)=0) ∧
        ∀ (ν : Measure 𝔸[ℚ]) [ν.IsAddHaarMeasure],
          NumberField.TateGlobal.ideleNorm ℚ c⁻¹ ≤ (V ν*∑' q : ℚ,fourierIntegral χ ν f (D q)).re) ∧
    ∀ (a : 𝔸[ℚ]ˣ) (f : 𝔸[ℚ]→ℂ), f∈schwartzBruhat ℚ → ∀ x : 𝔸[ℚ],
      (∑' q : ℚ,f (x+(a:𝔸[ℚ])*D q)) =
        V μ * (NumberField.TateGlobal.ideleNorm ℚ a:ℂ)⁻¹ *
          ∑' q : ℚ, let w := (((a*c)⁻¹:𝔸[ℚ]ˣ):𝔸[ℚ])*D q
              fourierIntegral χ μ f w * χ (w*x) := by sorry

end MasulloRH
