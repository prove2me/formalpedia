-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_exists_re_of_norm_qs_lt
-- name    : GroundTheory.Automorphic.GodementJacquet.exists_re_of_norm_qs_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:24:03.288923+00:00
-- url     : https://prove2.me/theorems/6a5474dc-8c03-53d2-8283-95e6deafaae9
-- title:
--   Godement Jacquet: exists re of norm qs lt
-- statement:
--   The Godement Jacquet construction uses the exists re of norm qs lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L253-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L253-L261

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

theorem GroundTheory.Automorphic.GodementJacquet.exists_re_of_norm_qs_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → ‖qs F s‖ < ε := by sorry
