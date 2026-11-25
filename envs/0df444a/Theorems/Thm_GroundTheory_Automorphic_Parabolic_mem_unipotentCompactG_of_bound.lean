-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompactG_of_bound
-- name    : GroundTheory.Automorphic.Parabolic.mem_unipotentCompactG_of_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:00.442797+00:00
-- url     : https://prove2.me/theorems/65970886-9e98-4cc6-b25d-45bc95c01e9b
-- title:
--   Parabolic: mem unipotent Compact G of bound
-- statement:
--   The Parabolic construction uses the mem unipotent Compact G of bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L93-L98

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable (γ : Fin n → ℕ)
variable {γ}

theorem GroundTheory.Automorphic.Parabolic.mem_unipotentCompactG_of_bound {e : ℕ} {u : GL (Fin n) F}
    (hu : u ∈ unipotentRadical F n γ)
    (hb : EntryBound F e (u : Matrix (Fin n) (Fin n) F))
    (hb' : EntryBound F e ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    u ∈ unipotentCompactG γ e := by sorry
