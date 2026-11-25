-- Prove2me | Theorems.Thm_GlobalTheory_PlaceInt_placeIdem
-- name    : GlobalTheory.PlaceInt.placeIdem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:12:09.883378+00:00
-- url     : https://prove2.me/theorems/3bcf8c6e-f344-4640-b3f8-2e04068e5e1f
-- title:
--   Place Int: place Idem
-- statement:
--   The Place Int construction uses the place Idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsRingOfIntegersLift.lean#L33-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsRingOfIntegersLift.lean#L33-L150

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
open NumberField Polynomial IsLocalRing

theorem GlobalTheory.PlaceInt.placeIdem : _root_.ReciprocityTheory.ChartRestriction.G.PullbackSections.PlaceIdemSt := by sorry
