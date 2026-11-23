-- Prove2me | Theorems.Thm_GlobalTheory_exists_bruhat_function_closed_subgroup
-- name    : GlobalTheory.exists_bruhat_function_closed_subgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:48.221603+00:00
-- url     : https://prove2.me/theorems/771cd225-a5dd-426b-af30-85b906397214
-- title:
--   Global Theory: exists bruhat function closed subgroup
-- statement:
--   The Global Theory construction uses the exists bruhat function closed subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsBruhatFunctionClosedSubgroup.lean#L149-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsBruhatFunctionClosedSubgroup.lean#L149-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
open GlobalTheory
open MeasureTheory
open scoped ENNReal

theorem GlobalTheory.exists_bruhat_function_closed_subgroup
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure] :
    ∃ φ : G → ℝ≥0∞, Measurable φ ∧ (∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1) ∧
      ∀ K : Set G, IsCompact K → ∃ (K' : Set G) (C : ℝ≥0∞), IsCompact K' ∧ C < ⊤ ∧
        ∀ k ∈ K, ∀ h : H, φ (k * h) ≤ C ∧ (φ (k * h) ≠ 0 → k * h ∈ K') := by sorry
