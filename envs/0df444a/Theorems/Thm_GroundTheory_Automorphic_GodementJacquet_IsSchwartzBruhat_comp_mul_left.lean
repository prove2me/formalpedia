-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_IsSchwartzBruhat_comp_mul_left
-- name    : GroundTheory.Automorphic.GodementJacquet.IsSchwartzBruhat.comp_mul_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:24:07.352562+00:00
-- url     : https://prove2.me/theorems/ada3954c-aec1-59cd-8252-fb75dc33b7be
-- title:
--   Is Schwartz Bruhat: comp mul left
-- statement:
--   The Is Schwartz Bruhat construction uses the comp mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L226-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L226-L235

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

theorem GroundTheory.Automorphic.GodementJacquet.IsSchwartzBruhat.comp_mul_left {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ)
    (a : GL (Fin n) F) : IsSchwartzBruhat fun X => Φ ((a : Matrix (Fin n) (Fin n) F) * X) := by sorry
