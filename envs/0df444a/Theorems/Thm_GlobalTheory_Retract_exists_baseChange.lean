-- Prove2me | Theorems.Thm_GlobalTheory_Retract_exists_baseChange
-- name    : GlobalTheory.Retract.exists_baseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:27.195651+00:00
-- url     : https://prove2.me/theorems/8bf1e327-50d9-40bf-8700-0056cc94c3db
-- title:
--   Retract: exists base Change
-- statement:
--   The Retract construction uses the exists base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L158-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L158-L165

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

theorem GlobalTheory.Retract.exists_baseChange (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) {T X' Y' : Scheme.{u}} {y : T ⟶ S}
    {a : X' ⟶ X} {f' : X' ⟶ T} (hX : IsPullback a f' f y)
    {b : Y' ⟶ Y} {g' : Y' ⟶ T} (hY : IsPullback b g' g y) :
    ∃ (i' : X' ⟶ Y') (r' : Y' ⟶ X'), i' ≫ r' = 𝟙 X' ∧ r' ≫ f' = g' ∧
      i' ≫ b = a ≫ i ∧ r' ≫ a = b ≫ r := by sorry
