-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_isClopen_shell
-- name    : GroundTheory.Automorphic.GodementJacquet.isClopen_shell
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:08.40246+00:00
-- url     : https://prove2.me/theorems/223a0164-06e7-4ba5-8f4a-d7319fa6826f
-- title:
--   Godement Jacquet: is Clopen shell
-- statement:
--   The Godement Jacquet construction uses the is Clopen shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L59-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L59-L74

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

theorem GroundTheory.Automorphic.GodementJacquet.isClopen_shell (k : ℤ) : IsClopen {g : GL (Fin n) F | ordDet g = k} := by sorry
