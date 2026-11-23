-- Prove2me | Theorems.Thm_GlobalTheory_SBExtend_indicator_mem_SB
-- name    : GlobalTheory.SBExtend.indicator_mem_SB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:27.477692+00:00
-- url     : https://prove2.me/theorems/30aa967c-658d-4fa1-939a-6cd8d9a944d0
-- title:
--   SBExtend: indicator mem SB
-- statement:
--   The SBExtend construction uses the indicator mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LocallyConstantExtensionByZero.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LocallyConstantExtensionByZero.lean#L36-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.SBExtend
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
open Matrix Topology
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

theorem GlobalTheory.SBExtend.indicator_mem_SB {V : Set X} (hc : IsCompact V)
    (hV : IsClopen V) : (V.indicator fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.SplitWeil.SB X := by sorry
