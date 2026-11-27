-- Prove2me | Theorems.Thm_GlobalTheory_exists_closure_fac_iff
-- name    : GlobalTheory.exists_closure_fac_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:44:18.402157+00:00
-- url     : https://prove2.me/theorems/73683d4b-2c2e-5e3b-9d08-86fac3d9d9c4
-- title:
--   Global Theory: exists closure fac iff
-- statement:
--   The Global Theory construction uses the exists closure fac iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L182-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L182-L188

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
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
open GlobalTheory
noncomputable section
variable {W P T' T Z : Scheme.{u}} (j : W ⟶ P)

theorem GlobalTheory.exists_closure_fac_iff (t : T ⟶ P) :
    (∃ l : T ⟶ j.image, l ≫ j.imageι = t) ↔ j.ker ≤ t.ker := by sorry
