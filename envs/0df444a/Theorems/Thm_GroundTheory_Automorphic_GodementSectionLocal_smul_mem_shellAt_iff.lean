-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_smul_mem_shellAt_iff
-- name    : GroundTheory.Automorphic.GodementSectionLocal.smul_mem_shellAt_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:23.886498+00:00
-- url     : https://prove2.me/theorems/380540c9-b55f-55cd-a72c-60f4f75cdfcb
-- title:
--   Godement Section Local: smul mem shell At iff
-- statement:
--   The Godement Section Local construction uses the smul mem shell At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L385-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L385-L388

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

theorem GroundTheory.Automorphic.GodementSectionLocal.smul_mem_shellAt_iff (k m : ℤ) (x : Fin 2 → F) :
    ((unifPow k : Fˣ) : F) • x ∈ shellAt F m ↔ x ∈ shellAt F (m - k) := by sorry
