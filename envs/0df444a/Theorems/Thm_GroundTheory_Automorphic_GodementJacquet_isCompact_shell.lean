-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_isCompact_shell
-- name    : GroundTheory.Automorphic.GodementJacquet.isCompact_shell
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:31.773665+00:00
-- url     : https://prove2.me/theorems/fcb3b562-d448-435d-ba89-cdafe56b0109
-- title:
--   Godement Jacquet: is Compact shell
-- statement:
--   The Godement Jacquet construction uses the is Compact shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L78-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L78-L154

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe
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
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable (F n)

theorem GroundTheory.Automorphic.GodementJacquet.isCompact_shell (A : ℕ) (k : ℤ) :
    IsCompact {g : GL (Fin n) F | (∀ i j, (uniformizer F : F) ^ A * g i j ∈ 𝒪[F]) ∧ ordDet g = k} := by sorry
