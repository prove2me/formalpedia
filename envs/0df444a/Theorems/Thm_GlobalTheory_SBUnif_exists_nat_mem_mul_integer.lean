-- Prove2me | Theorems.Thm_GlobalTheory_SBUnif_exists_nat_mem_mul_integer
-- name    : GlobalTheory.SBUnif.exists_nat_mem_mul_integer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:46.061195+00:00
-- url     : https://prove2.me/theorems/cca0ce63-b431-4916-8d7c-1354f6f337a9
-- title:
--   SBUnif: exists nat mem mul integer
-- statement:
--   The SBUnif construction uses the exists nat mem mul integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsNeZeroOfEventually.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsNeZeroOfEventually.lean#L10-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.SBUnif
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SBUnif.exists_nat_mem_mul_integer (c : k) (hc : c ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ c⁻¹ * (n : k) ∈ 𝒪[k] := by sorry
