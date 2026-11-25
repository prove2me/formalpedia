-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localSection_mem_smoothPrincipalSeries
-- name    : GroundTheory.Automorphic.GodementSectionLocal.localSection_mem_smoothPrincipalSeries
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:45.75082+00:00
-- url     : https://prove2.me/theorems/abedaf46-0c74-5231-bbd4-21358667a4db
-- title:
--   Godement Section Local: local Section mem smooth Principal Series
-- statement:
--   The Godement Section Local construction uses the local Section mem smooth Principal Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L966-L969
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L966-L969

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

theorem GroundTheory.Automorphic.GodementSectionLocal.localSection_mem_smoothPrincipalSeries {χ₁ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁)
    (χ₂ : Fˣ →* ℂˣ) (s : ℂ) {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    localSection χ₁ χ₂ s Φ ∈ smoothPrincipalSeries χ₁ χ₂ s := by sorry
