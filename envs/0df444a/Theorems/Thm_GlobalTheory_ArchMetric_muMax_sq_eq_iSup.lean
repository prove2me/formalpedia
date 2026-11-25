-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_muMax_sq_eq_iSup
-- name    : GlobalTheory.ArchMetric.muMax_sq_eq_iSup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:01:31.41383+00:00
-- url     : https://prove2.me/theorems/b7b5f838-535b-4e33-b4d6-55210b34b3c4
-- title:
--   Arch Metric: mu Max sq eq i Sup
-- statement:
--   The Arch Metric construction uses the mu Max sq eq i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L1192-L1198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L1192-L1198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
variable {A B : Submodule (𝓞 K) V}

theorem GlobalTheory.ArchMetric.muMax_sq_eq_iSup (A : Submodule (𝓞 K) V) :
    h.muMax_sq A = ⨆ (B : Submodule (𝓞 K) V) (_ : B ≤ A) (_ : B ≠ ⊥), (h.slope_sq B : EReal) := by sorry
