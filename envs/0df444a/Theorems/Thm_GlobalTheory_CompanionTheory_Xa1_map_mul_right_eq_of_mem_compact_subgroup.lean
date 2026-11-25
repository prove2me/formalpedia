-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Xa1_map_mul_right_eq_of_mem_compact_subgroup
-- name    : GlobalTheory.CompanionTheory.Xa1.map_mul_right_eq_of_mem_compact_subgroup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:01:55.518605+00:00
-- url     : https://prove2.me/theorems/bf64e617-2e06-5589-b1b5-9e98cae1ca41
-- title:
--   Xa1: map mul right eq of mem compact subgroup
-- statement:
--   The Xa1 construction uses the map mul right eq of mem compact subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/MapMulRightEqOfMemCompactSubgroup.lean#L8-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/MapMulRightEqOfMemCompactSubgroup.lean#L8-L44

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AdelicProofs_MapMulRightEqOfMemCompactSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Xa1

theorem GlobalTheory.CompanionTheory.Xa1.map_mul_right_eq_of_mem_compact_subgroup :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsMulLeftInvariant → IsFiniteMeasureOnCompacts μ → ∀ K : Subgroup G, IsCompact (K : Set G) → ∀ k ∈ K, μ.map (fun x => x * k) = μ := by sorry
