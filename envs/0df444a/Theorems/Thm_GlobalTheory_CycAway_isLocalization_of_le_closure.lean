-- Prove2me | Theorems.Thm_GlobalTheory_CycAway_isLocalization_of_le_closure
-- name    : GlobalTheory.CycAway.isLocalization_of_le_closure
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:34:18.214593+00:00
-- url     : https://prove2.me/theorems/395b98bc-25c9-460a-af78-591cc371a44b
-- title:
--   Cyc Away: is Localization of le closure
-- statement:
--   The Cyc Away construction uses the is Localization of le closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsLocalizationOfLeClosure.lean#L16-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsLocalizationOfLeClosure.lean#L16-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsLocalizationOfLeClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.CycAway
open NumberField

theorem GlobalTheory.CycAway.isLocalization_of_le_closure {Ω : Type} [Field Ω] {n : ℕ} (h0 : (n : Ω) ≠ 0) (A : Type) [CommRing A]
    (T : Subring Ω) [Algebra A T] (hinj : Function.Injective (algebraMap A T)) (hinv : (n : Ω)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ({x | ∃ a, x = (algebraMap A T a : Ω)} ∪ {(n : Ω)⁻¹})) :
    IsLocalization (Submonoid.powers (n : A)) T := by sorry
