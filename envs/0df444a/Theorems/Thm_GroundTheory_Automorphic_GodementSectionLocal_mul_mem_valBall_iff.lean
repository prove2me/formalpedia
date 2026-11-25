-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_mul_mem_valBall_iff
-- name    : GroundTheory.Automorphic.GodementSectionLocal.mul_mem_valBall_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:25.590845+00:00
-- url     : https://prove2.me/theorems/23274350-b5e3-542a-a889-c0c064940bf5
-- title:
--   Godement Section Local: mul mem val Ball iff
-- statement:
--   The Godement Section Local construction uses the mul mem val Ball iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L350-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L350-L356

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

theorem GroundTheory.Automorphic.GodementSectionLocal.mul_mem_valBall_iff (a : Fˣ) (n : ℤ) (y : F) :
    (a : F) * y ∈ valBall F n ↔ y ∈ valBall F (n - ord (a : F)) := by sorry
