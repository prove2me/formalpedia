-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localSection_smul
-- name    : GroundTheory.Automorphic.GodementSectionLocal.localSection_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:29.923642+00:00
-- url     : https://prove2.me/theorems/682cbcb5-a8bb-5cf1-b868-67145c638809
-- title:
--   Godement Section Local: local Section smul
-- statement:
--   The Godement Section Local construction uses the local Section smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L207-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L207-L219

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

theorem GroundTheory.Automorphic.GodementSectionLocal.localSection_smul (χ₁ χ₂ : Fˣ →* ℂˣ) (s c : ℂ) (Φ : (Fin 2 → F) → ℂ) :
    localSection χ₁ χ₂ s (c • Φ) = c • localSection χ₁ χ₂ s Φ := by sorry
