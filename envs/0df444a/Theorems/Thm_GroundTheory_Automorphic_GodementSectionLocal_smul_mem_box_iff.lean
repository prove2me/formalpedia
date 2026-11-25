-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_smul_mem_box_iff
-- name    : GroundTheory.Automorphic.GodementSectionLocal.smul_mem_box_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:15.189875+00:00
-- url     : https://prove2.me/theorems/ef63414a-f110-422a-841c-54bf9c592105
-- title:
--   Godement Section Local: smul mem box iff
-- statement:
--   The Godement Section Local construction uses the smul mem box iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L360-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L360-L362

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
omit [MeasurableSpace F] [BorelSpace F]

theorem GroundTheory.Automorphic.GodementSectionLocal.smul_mem_box_iff (a : Fˣ) (n : ℤ) (x : Fin 2 → F) :
    (a : F) • x ∈ box F n ↔ x ∈ box F (n - ord (a : F)) := by sorry
