-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_ordDet_of_mem_integralGL
-- name    : GroundTheory.Automorphic.GodementJacquet.ordDet_of_mem_integralGL
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:24:09.762179+00:00
-- url     : https://prove2.me/theorems/194bcf9f-12cf-526e-b4d8-785dc28766df
-- title:
--   Godement Jacquet: ord Det of mem integral GL
-- statement:
--   The Godement Jacquet construction uses the ord Det of mem integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L41-L51

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

theorem GroundTheory.Automorphic.GodementJacquet.ordDet_of_mem_integralGL {k : GL (Fin n) F} (hk : k ∈ integralGL F n) : ordDet k = 0 := by sorry
