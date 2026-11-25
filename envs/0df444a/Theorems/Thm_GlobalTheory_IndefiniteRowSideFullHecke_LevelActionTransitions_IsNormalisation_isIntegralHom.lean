-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LevelActionTransitions_IsNormalisation_isIntegralHom
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions.IsNormalisation.isIntegralHom
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:04.355969+00:00
-- url     : https://prove2.me/theorems/d5a48385-6598-5d07-8ac8-18d6fb4a8cd3
-- title:
--   Is Normalisation: is Integral Hom
-- statement:
--   The Is Normalisation construction uses the is Integral Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LevelActionTransitions.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LevelActionTransitions.lean#L102-L105

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions.IsNormalisation.isIntegralHom {U Z Y : Scheme.{0}} {i : U ⟶ Z} {p : Z ⟶ Y} (h : IsNormalisation i p) :
    IsIntegralHom p := by sorry
