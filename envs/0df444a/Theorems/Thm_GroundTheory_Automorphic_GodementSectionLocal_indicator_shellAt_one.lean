-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_indicator_shellAt_one
-- name    : GroundTheory.Automorphic.GodementSectionLocal.indicator_shellAt_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:08.312028+00:00
-- url     : https://prove2.me/theorems/e979310d-3a7e-5d7a-981c-42eef0a18f1e
-- title:
--   Godement Section Local: indicator shell At one
-- statement:
--   The Godement Section Local construction uses the indicator shell At one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L572-L575
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L572-L575

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

theorem GroundTheory.Automorphic.GodementSectionLocal.indicator_shellAt_one (n : ℤ) :
    (shellAt F n).indicator (1 : (Fin 2 → F) → ℂ) =
      fun x ↦ shellInd F (((unifPow (-n) : Fˣ) : F) • x) := by sorry
