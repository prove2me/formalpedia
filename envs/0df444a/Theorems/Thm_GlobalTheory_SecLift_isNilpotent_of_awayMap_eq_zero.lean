-- Prove2me | Theorems.Thm_GlobalTheory_SecLift_isNilpotent_of_awayMap_eq_zero
-- name    : GlobalTheory.SecLift.isNilpotent_of_awayMap_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:51:18.387421+00:00
-- url     : https://prove2.me/theorems/51f83f95-543e-48f1-9843-33661bd7c4a4
-- title:
--   Sec Lift: is Nilpotent of away Map eq zero
-- statement:
--   The Sec Lift construction uses the is Nilpotent of away Map eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSectionLiftBasicOpenAffine.lean#L16-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSectionLiftBasicOpenAffine.lean#L16-L37

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

theorem GlobalTheory.SecLift.isNilpotent_of_awayMap_eq_zero (π : R →+* R₀) (hnil : IsNilpotent (RingHom.ker π)) (f : R)
    (x : Localization.Away f) (hx : Localization.awayMap π f x = 0) : IsNilpotent x := by sorry
