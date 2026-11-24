-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_IsRestrGroup_isOpen_levelAway
-- name    : GlobalTheory.RestrMeas.IsRestrGroup.isOpen_levelAway
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:21:19.487798+00:00
-- url     : https://prove2.me/theorems/85f90daf-894f-41b5-aec6-4543032d8a89
-- title:
--   Is Restr Group: is Open level Away
-- statement:
--   The Is Restr Group construction uses the is Open level Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L210-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L210-L216

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]
variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}

theorem GlobalTheory.RestrMeas.IsRestrGroup.isOpen_levelAway [IsTopologicalGroup X] (h : IsRestrGroup pa pf K) (S : Finset V) :
    IsOpen (levelAway pf K S : Set X) := by sorry
