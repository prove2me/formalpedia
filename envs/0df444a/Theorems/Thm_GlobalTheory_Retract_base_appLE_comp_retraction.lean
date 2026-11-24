-- Prove2me | Theorems.Thm_GlobalTheory_Retract_base_appLE_comp_retraction
-- name    : GlobalTheory.Retract.base_appLE_comp_retraction
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:20:50.203208+00:00
-- url     : https://prove2.me/theorems/7101d9dd-d9be-4600-8df9-9d2f09b382f4
-- title:
--   Retract: base app LE comp retraction
-- statement:
--   The Retract construction uses the base app LE comp retraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L130-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L130-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}

theorem GlobalTheory.Retract.base_appLE_comp_retraction (hr : r ≫ f = g) {U : X.Opens} {V : Y.Opens} {W : S.Opens}
    (hVU : V ≤ r ⁻¹ᵁ U) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    f.appLE W U hUW ≫ r.appLE U V hVU = g.appLE W V hVW := by sorry
