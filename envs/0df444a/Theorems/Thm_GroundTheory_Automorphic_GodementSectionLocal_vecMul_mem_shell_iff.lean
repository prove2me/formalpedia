-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_vecMul_mem_shell_iff
-- name    : GroundTheory.Automorphic.GodementSectionLocal.vecMul_mem_shell_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:55.232281+00:00
-- url     : https://prove2.me/theorems/15404c1d-978d-5380-a564-e54dce2affb6
-- title:
--   Godement Section Local: vec Mul mem shell iff
-- statement:
--   The Godement Section Local construction uses the vec Mul mem shell iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L723-L725
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L723-L725

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

theorem GroundTheory.Automorphic.GodementSectionLocal.vecMul_mem_shell_iff {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2)
    (x : Fin 2 → F) : x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ shell F ↔ x ∈ shell F := by sorry
