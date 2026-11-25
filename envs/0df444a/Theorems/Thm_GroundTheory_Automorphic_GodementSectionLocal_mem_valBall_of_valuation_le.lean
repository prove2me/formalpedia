-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_mem_valBall_of_valuation_le
-- name    : GroundTheory.Automorphic.GodementSectionLocal.mem_valBall_of_valuation_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:24.407158+00:00
-- url     : https://prove2.me/theorems/c3d6b0d5-670f-57b3-b8d1-f093fcc3d91d
-- title:
--   Godement Section Local: mem val Ball of valuation le
-- statement:
--   The Godement Section Local construction uses the mem val Ball of valuation le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L870-L877
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L870-L877

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

theorem GroundTheory.Automorphic.GodementSectionLocal.mem_valBall_of_valuation_le {y : F} {m : ℕ}
    (hy : ValuativeRel.valuation F y ≤ ValuativeRel.valuation F (GLnLocal.uniformizer F : F) ^ m) :
    y ∈ valBall F m := by sorry
