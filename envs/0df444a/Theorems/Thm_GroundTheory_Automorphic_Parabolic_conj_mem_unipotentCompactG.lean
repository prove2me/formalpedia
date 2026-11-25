-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_mem_unipotentCompactG
-- name    : GroundTheory.Automorphic.Parabolic.conj_mem_unipotentCompactG
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:32.344153+00:00
-- url     : https://prove2.me/theorems/081f233b-ba91-57e5-a263-68c4250dac6a
-- title:
--   Parabolic: conj mem unipotent Compact G
-- statement:
--   The Parabolic construction uses the conj mem unipotent Compact G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L223-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L223-L238

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {γ : Fin n → ℕ}

theorem GroundTheory.Automorphic.Parabolic.conj_mem_unipotentCompactG {k u : GL (Fin n) F} (hk : k ∈ levi F n γ)
    (hk' : k ∈ integralGL F n) {e : ℕ} (hu : u ∈ unipotentCompactG γ e) :
    k * u * k⁻¹ ∈ unipotentCompactG γ e := by sorry
