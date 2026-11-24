-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_isCompact_finset_sup
-- name    : GlobalTheory.JR.WeilQuad.Fnf.isCompact_finset_sup
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:38:52.279741+00:00
-- url     : https://prove2.me/theorems/eacb2d33-8a3c-4de4-b57a-08dc18833321
-- title:
--   Fnf: is Compact finset sup
-- statement:
--   The Fnf construction uses the is Compact finset sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFOpNOpFOpGauss.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFOpNOpFOpGauss.lean#L37-L43

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

theorem GlobalTheory.JR.WeilQuad.Fnf.isCompact_finset_sup {V ι : Type} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V]
    (t : Finset ι) (H : ι → AddSubgroup V) (hH : ∀ i, IsCompact (H i : Set V)) :
    IsCompact ((t.sup H : AddSubgroup V) : Set V) := by sorry
