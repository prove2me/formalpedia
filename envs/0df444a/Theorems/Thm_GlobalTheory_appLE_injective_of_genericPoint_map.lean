-- Prove2me | Theorems.Thm_GlobalTheory_appLE_injective_of_genericPoint_map
-- name    : GlobalTheory.appLE_injective_of_genericPoint_map
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:36.66374+00:00
-- url     : https://prove2.me/theorems/2ef66155-9b07-4ee0-a128-0fc1587f35e9
-- title:
--   Global Theory: app LE injective of generic Point map
-- statement:
--   The Global Theory construction uses the app LE injective of generic Point map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AppLEInjectiveOfGenericPointMap.lean#L5-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AppLEInjectiveOfGenericPointMap.lean#L5-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AppLEInjectiveOfGenericPointMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory

theorem GlobalTheory.appLE_injective_of_genericPoint_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (π : Y ⟶ X) (hπ : π (genericPoint Y) = genericPoint X) {U : X.Opens} {V : Y.Opens}
    (hV : (V : Set Y).Nonempty) (h : V ≤ π ⁻¹ᵁ U) :
    Function.Injective (π.appLE U V h).hom := by sorry
