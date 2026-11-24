-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_exists_big
-- name    : GlobalTheory.JR.WeilQuad.Fnf.exists_big
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:40:13.497472+00:00
-- url     : https://prove2.me/theorems/f7a50528-65bc-4fcc-a6ed-ee11ec05c9e3
-- title:
--   Fnf: exists big
-- statement:
--   The Fnf construction uses the exists big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFOpNOpFOpGauss.lean#L45-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFOpNOpFOpGauss.lean#L45-L72

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

theorem GlobalTheory.JR.WeilQuad.Fnf.exists_big {F V : Type} [NontriviallyNormedField F] [AddCommGroup V] [Module F V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul F V]
    (Λ₀ : AddSubgroup V) (ho : IsOpen (Λ₀ : Set V)) (hc : IsCompact (Λ₀ : Set V)) (C : Set V)
    (hC : IsCompact C) :
    ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧ Λ₀ ≤ Λ ∧ C ⊆ Λ := by sorry
