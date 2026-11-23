-- Prove2me | Theorems.Thm_GlobalTheory_Retract_appLE_comp_appLE
-- name    : GlobalTheory.Retract.appLE_comp_appLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:51.138716+00:00
-- url     : https://prove2.me/theorems/5af922ad-8b7e-4e64-ae06-d108ab911f5b
-- title:
--   Retract: app LE comp app LE
-- statement:
--   The Retract construction uses the app LE comp app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L120-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L120-L128

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

theorem GlobalTheory.Retract.appLE_comp_appLE (hir : i ≫ r = 𝟙 X) {U : X.Opens} {V : Y.Opens}
    (hUV : U ≤ i ⁻¹ᵁ V) (hVU : V ≤ r ⁻¹ᵁ U) :
    r.appLE U V hVU ≫ i.appLE V U hUV = 𝟙 Γ(X, U) := by sorry
