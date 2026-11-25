-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localZeta_mul_right
-- name    : GroundTheory.Automorphic.GodementSectionLocal.localZeta_mul_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:51:54.507187+00:00
-- url     : https://prove2.me/theorems/bccbaa12-66ba-59c7-bbaa-bb9e1767e34d
-- title:
--   Godement Section Local: local Zeta mul right
-- statement:
--   The Godement Section Local construction uses the local Zeta mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L116-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L116-L135

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

theorem GroundTheory.Automorphic.GodementSectionLocal.localZeta_mul_right (f : F → ℂ) (μ : Fˣ →* ℂˣ) (s : ℂ) (d : Fˣ) :
    localZeta (fun t ↦ f (t * d)) μ s =
      (((μ d)⁻¹ : ℂˣ) : ℂ) * modPow (d : F) (-s) * localZeta f μ s := by sorry
