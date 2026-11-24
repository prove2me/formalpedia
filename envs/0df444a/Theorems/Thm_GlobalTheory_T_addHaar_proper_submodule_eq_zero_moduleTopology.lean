-- Prove2me | Theorems.Thm_GlobalTheory_T_addHaar_proper_submodule_eq_zero_moduleTopology
-- name    : GlobalTheory.T.addHaar_proper_submodule_eq_zero_moduleTopology
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:26:23.596274+00:00
-- url     : https://prove2.me/theorems/13758308-e758-4069-a8bd-369af892d384
-- title:
--   T: add Haar proper submodule eq zero module Topology
-- statement:
--   The T construction uses the add Haar proper submodule eq zero module Topology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddHaarProperSubmoduleEqZeroModuleTopologyStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddHaarProperSubmoduleEqZeroModuleTopologyStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddHaarProperSubmoduleEqZeroModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddHaarProperSubmoduleEqZeroModuleTopologyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.addHaar_proper_submodule_eq_zero_moduleTopology : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ s : Submodule F V, s ≠ ⊤ → μ (s : Set V) = 0 := by sorry
