-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_mem_schwartzBruhat2
-- name    : GroundTheory.Automorphic.GodementSectionLocal.mem_schwartzBruhat2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:10.82404+00:00
-- url     : https://prove2.me/theorems/e2b6a061-5936-5a91-8700-58fadb7dcf42
-- title:
--   Godement Section Local: mem schwartz Bruhat2
-- statement:
--   The Godement Section Local construction uses the mem schwartz Bruhat2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L26-L27

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

theorem GroundTheory.Automorphic.GodementSectionLocal.mem_schwartzBruhat2 {Φ : (Fin 2 → F) → ℂ} :
    Φ ∈ schwartzBruhat2 F ↔ IsLocallyConstant Φ ∧ HasCompactSupport Φ := by sorry
