-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LevelActionTransitions_isNormalisation_normalization
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions.isNormalisation_normalization
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:43.237866+00:00
-- url     : https://prove2.me/theorems/2b4a6851-9866-5c91-915b-6a6e164aa492
-- title:
--   Level Action Transitions: is Normalisation normalization
-- statement:
--   The Level Action Transitions construction uses the is Normalisation normalization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LevelActionTransitions.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LevelActionTransitions.lean#L94-L100

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions.isNormalisation_normalization {U Y : Scheme.{0}} (f : U ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    IsNormalisation f.toNormalization f.fromNormalization := by sorry
