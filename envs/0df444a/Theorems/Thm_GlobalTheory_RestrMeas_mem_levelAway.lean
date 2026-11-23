-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_mem_levelAway
-- name    : GlobalTheory.RestrMeas.mem_levelAway
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:56.461424+00:00
-- url     : https://prove2.me/theorems/446c9a13-d038-40e9-b4c7-260a6de18d48
-- title:
--   Restr Meas: mem level Away
-- statement:
--   The Restr Meas construction uses the mem level Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L207-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L207-L208

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
omit [TopologicalSpace X] [∀ v, TopologicalSpace (Yf v)]

theorem GlobalTheory.RestrMeas.mem_levelAway {S : Finset V} {x : X} : x ∈ levelAway pf K S ↔ ∀ v ∉ S, pf v x ∈ K v := by sorry
