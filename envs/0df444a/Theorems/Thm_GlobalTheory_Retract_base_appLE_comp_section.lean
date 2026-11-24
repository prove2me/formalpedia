-- Prove2me | Theorems.Thm_GlobalTheory_Retract_base_appLE_comp_section
-- name    : GlobalTheory.Retract.base_appLE_comp_section
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:20:43.035432+00:00
-- url     : https://prove2.me/theorems/89de069e-9191-4abe-a874-c6da9ec762ce
-- title:
--   Retract: base app LE comp section
-- statement:
--   The Retract construction uses the base app LE comp section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L136-L140

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

theorem GlobalTheory.Retract.base_appLE_comp_section (hi : i ≫ g = f) {U : X.Opens} {V : Y.Opens} {W : S.Opens}
    (hUV : U ≤ i ⁻¹ᵁ V) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    g.appLE W V hVW ≫ i.appLE V U hUV = f.appLE W U hUW := by sorry
