-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_mem_unipotentRadical
-- name    : GroundTheory.Automorphic.Parabolic.conj_mem_unipotentRadical
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:41:26.011143+00:00
-- url     : https://prove2.me/theorems/a2915be3-0c7a-4d52-a3bd-f59165225b64
-- title:
--   Parabolic: conj mem unipotent Radical
-- statement:
--   The Parabolic construction uses the conj mem unipotent Radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L174-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L174-L182

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa
variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}

theorem GroundTheory.Automorphic.Parabolic.conj_mem_unipotentRadical {p u : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (hu : u ∈ unipotentRadical F n β) : p * u * p⁻¹ ∈ unipotentRadical F n β := by sorry
