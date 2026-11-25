-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_indicator_mem_schwartzBruhat2
-- name    : GroundTheory.Automorphic.GodementSectionLocal.indicator_mem_schwartzBruhat2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:37.704003+00:00
-- url     : https://prove2.me/theorems/77400927-8521-52a3-bf29-72a9876ab670
-- title:
--   Godement Section Local: indicator mem schwartz Bruhat2
-- statement:
--   The Godement Section Local construction uses the indicator mem schwartz Bruhat2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L404-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L404-L408

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

theorem GroundTheory.Automorphic.GodementSectionLocal.indicator_mem_schwartzBruhat2 {S : Set (Fin 2 → F)} (hS : IsClopen S) {n : ℤ}
    (hSn : S ⊆ box F n) {f : (Fin 2 → F) → ℂ} (hf : IsLocallyConstant f) :
    S.indicator f ∈ schwartzBruhat2 F := by sorry
