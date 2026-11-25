-- Prove2me | Theorems.Thm_GlobalTheory_T_haar_measure_subgroup_relIndex_mul
-- name    : GlobalTheory.T.haar_measure_subgroup_relIndex_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:32:00.975788+00:00
-- url     : https://prove2.me/theorems/c8bc8f05-1d43-4528-b1b6-063ecb67b036
-- title:
--   T: haar measure subgroup rel Index mul
-- statement:
--   The T construction uses the haar measure subgroup rel Index mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSubgroupRelIndexMulStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSubgroupRelIndexMulStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSubgroupRelIndexMul
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSubgroupRelIndexMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.haar_measure_subgroup_relIndex_mul : ∀ (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G), H ≤ K → MeasurableSet (H : Set G) → H.relIndex K ≠ 0 → μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by sorry
