-- Prove2me | Theorems.Thm_GlobalTheory_PlaceInt_exists_ringOfIntegers_lift
-- name    : GlobalTheory.PlaceInt.exists_ringOfIntegers_lift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:03:21.377284+00:00
-- url     : https://prove2.me/theorems/b4096852-7476-4910-97c3-f165f920fe23
-- title:
--   Place Int: exists ring Of Integers lift
-- statement:
--   The Place Int construction uses the exists ring Of Integers lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsRingOfIntegersLift.lean#L12-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsRingOfIntegersLift.lean#L12-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_PlaceIdem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSCCols
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsRingOfIntegersLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.PlaceInt
open NumberField

theorem GlobalTheory.PlaceInt.exists_ringOfIntegers_lift (E : Type) [Field E] [NumberField E]
    (V : Type) [CommRing V]
    [IsDomain V] [IsIntegrallyClosed V] (k : Type) [Field k] [Algebra V k] [IsFractionRing V k]
    (ψ : E →+* k) :
    ∃ σ : 𝓞 E →+* V, ∀ x : 𝓞 E, algebraMap V k (σ x) = ψ (x : E) := by sorry
