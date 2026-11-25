-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_detPow_mul
-- name    : GroundTheory.Automorphic.GodementJacquet.detPow_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:29:35.326536+00:00
-- url     : https://prove2.me/theorems/e7bddbf3-a28b-5820-bf80-f89125412e17
-- title:
--   Godement Jacquet: det Pow mul
-- statement:
--   The Godement Jacquet construction uses the det Pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L25-L28

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

theorem GroundTheory.Automorphic.GodementJacquet.detPow_mul (g h : GL (Fin n) F) (s : ℂ) :
    detPow (g * h) s = detPow g s * detPow h s := by sorry
