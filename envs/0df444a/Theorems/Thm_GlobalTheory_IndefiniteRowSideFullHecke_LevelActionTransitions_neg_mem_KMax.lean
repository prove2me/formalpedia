-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LevelActionTransitions_neg_mem_KMax
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions.neg_mem_KMax
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:56.230872+00:00
-- url     : https://prove2.me/theorems/eb79b6eb-ac05-53b0-8040-9c1ca168a1b6
-- title:
--   Level Action Transitions: neg mem KMax
-- statement:
--   The Level Action Transitions construction uses the neg mem KMax property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LevelActionTransitions.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LevelActionTransitions.lean#L69-L72

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
variable (D : Datum H)

theorem GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions.neg_mem_KMax : (fun n => LinearEquiv.neg (𝓞 E)) ∈ KMax D := by sorry
