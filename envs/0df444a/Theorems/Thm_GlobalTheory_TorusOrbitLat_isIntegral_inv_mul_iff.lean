-- Prove2me | Theorems.Thm_GlobalTheory_TorusOrbitLat_isIntegral_inv_mul_iff
-- name    : GlobalTheory.TorusOrbitLat.isIntegral_inv_mul_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:11:04.416255+00:00
-- url     : https://prove2.me/theorems/5ad59c4b-53eb-458e-96d1-f0b0eafdd372
-- title:
--   Torus Orbit Lat: is Integral inv mul iff
-- statement:
--   The Torus Orbit Lat construction uses the is Integral inv mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorusOrbitLatticeCountBoundedByRho.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorusOrbitLatticeCountBoundedByRho.lean#L43-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusOrbitLatticeCountBoundedByRho
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.TorusOrbitLat
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

theorem GlobalTheory.TorusOrbitLat.isIntegral_inv_mul_iff (t u : Aˣ) (hu : u ∈ intUnits O A) (w : A) :
    IsIntegral O ((((t * u)⁻¹ : Aˣ) : A) * w) ↔ IsIntegral O (((t⁻¹ : Aˣ) : A) * w) := by sorry
