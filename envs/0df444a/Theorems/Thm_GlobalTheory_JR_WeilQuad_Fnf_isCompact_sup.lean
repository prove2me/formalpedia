-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_isCompact_sup
-- name    : GlobalTheory.JR.WeilQuad.Fnf.isCompact_sup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:11.846799+00:00
-- url     : https://prove2.me/theorems/a71cea58-5643-4ac3-8351-41e601423ec0
-- title:
--   Fnf: is Compact sup
-- statement:
--   The Fnf construction uses the is Compact sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFOpNOpFOpGauss.lean#L24-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFOpNOpFOpGauss.lean#L24-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.Fnf

theorem GlobalTheory.JR.WeilQuad.Fnf.isCompact_sup {V : Type} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V]
    (H K : AddSubgroup V) (hH : IsCompact (H : Set V)) (hK : IsCompact (K : Set V)) :
    IsCompact ((H ⊔ K : AddSubgroup V) : Set V) := by sorry
