-- Prove2me | Theorems.Thm_GlobalTheory_SecLift_awayMap_surjective_of_surjective
-- name    : GlobalTheory.SecLift.awayMap_surjective_of_surjective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:51:52.527784+00:00
-- url     : https://prove2.me/theorems/35ea4e1f-4d4c-436c-9b35-6def2cb8fc18
-- title:
--   Sec Lift: away Map surjective of surjective
-- statement:
--   The Sec Lift construction uses the away Map surjective of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSectionLiftBasicOpenAffine.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSectionLiftBasicOpenAffine.lean#L11-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_FiniteLocalLifts_SmLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSectionLiftBasicOpenAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecLift
variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem GlobalTheory.SecLift.awayMap_surjective_of_surjective (π : R →+* R₀) (hπ : Function.Surjective π) (f : R) :
    Function.Surjective (Localization.awayMap π f) := by sorry
