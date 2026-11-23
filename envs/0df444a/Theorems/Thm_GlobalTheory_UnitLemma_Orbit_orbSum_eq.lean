-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_orbSum_eq
-- name    : GlobalTheory.UnitLemma.Orbit.orbSum_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:10.617149+00:00
-- url     : https://prove2.me/theorems/d06888a1-fe61-470f-9e2b-fdeaa40bbba0
-- title:
--   Orbit: orb Sum eq
-- statement:
--   The Orbit construction uses the orb Sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L237-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L237-L243

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
variable {O : Type} [CommRing O] {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

theorem GlobalTheory.UnitLemma.Orbit.orbSum_eq (G : Subgroup Aˣ) (X : Set (Submodule O A)) :
    orbSum O G X (fun _ => 1) = ∑ᶠ o, orbWt G X o := by sorry
