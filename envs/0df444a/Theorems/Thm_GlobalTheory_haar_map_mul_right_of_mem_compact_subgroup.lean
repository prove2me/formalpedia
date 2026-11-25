-- Prove2me | Theorems.Thm_GlobalTheory_haar_map_mul_right_of_mem_compact_subgroup
-- name    : GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:05.816804+00:00
-- url     : https://prove2.me/theorems/e33bf602-dd50-4c1c-a823-eab3ff523b60
-- title:
--   Global Theory: haar map mul right of mem compact subgroup
-- statement:
--   The Global Theory construction uses the haar map mul right of mem compact subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarMapMulRightOfMemCompactSubgroup.lean#L8-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarMapMulRightOfMemCompactSubgroup.lean#L8-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapMulRightOfMemCompactSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise NNReal ENNReal
open GlobalTheory

theorem GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G) (hK : IsCompact (K : Set G))
    (k : G) (hk : k ∈ K) : Measure.map (fun g => g * k) μ = μ := by sorry
