-- Prove2me | Theorems.Thm_GlobalTheory_HaarNullSub_addHaar_submodule_eq_zero
-- name    : GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:00.587959+00:00
-- url     : https://prove2.me/theorems/4092c5b4-8f4f-4a14-b0ac-35b127103ef4
-- title:
--   Haar Null Sub: add Haar submodule eq zero
-- statement:
--   The Haar Null Sub construction uses the add Haar submodule eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddHaarProperSubmoduleEqZeroModuleTopology.lean#L8-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddHaarProperSubmoduleEqZeroModuleTopology.lean#L8-L85

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddHaarProperSubmoduleEqZeroModuleTopology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open Set Pointwise Metric
open GlobalTheory GlobalTheory.HaarNullSub

theorem GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F]
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V]
    [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    (hμ : μ.IsAddHaarMeasure) (s : Submodule F V) (hs : s ≠ ⊤) : μ (s : Set V) = 0 := by sorry
