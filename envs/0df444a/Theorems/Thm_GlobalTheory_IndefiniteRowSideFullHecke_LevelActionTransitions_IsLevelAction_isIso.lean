-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LevelActionTransitions_IsLevelAction_isIso
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions.IsLevelAction.isIso
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:26.440649+00:00
-- url     : https://prove2.me/theorems/780b1ed4-462e-5bc5-abdd-b8720dea3ea8
-- title:
--   Is Level Action: is Iso
-- statement:
--   The Is Level Action construction uses the is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LevelActionTransitions.lean#L143-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LevelActionTransitions.lean#L143-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_OpenModelSections
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LevelActionTransitions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
  {univ : Obj D l (baseKA l) str} {F₀ : IntermediateField ℚ ℂ} {h : IsCoeffField l F₀}
  {O : Type} [CommRing O] {φ : O →+* F₀}

theorem GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions.IsLevelAction.isIso {m : Model univ h φ} {act lift act₀} (ρ : IsLevelAction m act lift act₀) (g : KMax D) :
    IsIso (act g) := by sorry
