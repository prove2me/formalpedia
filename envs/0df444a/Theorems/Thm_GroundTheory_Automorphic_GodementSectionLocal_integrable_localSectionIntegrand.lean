-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_integrable_localSectionIntegrand
-- name    : GroundTheory.Automorphic.GodementSectionLocal.integrable_localSectionIntegrand
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:56.930396+00:00
-- url     : https://prove2.me/theorems/1a0b13a7-906f-5b7f-9d19-d9b0241de42e
-- title:
--   Godement Section Local: integrable local Section Integrand
-- statement:
--   The Godement Section Local construction uses the integrable local Section Integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L144-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L144-L149

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

theorem GroundTheory.Automorphic.GodementSectionLocal.integrable_localSectionIntegrand {χ₁ χ₂ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁)
    (h₂ : Continuous χ₂) {s : ℂ} (hs : -quasiCharExponent (χ₁ * χ₂⁻¹) < 2 * s.re)
    {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) (g : GL (Fin 2) F) :
    Integrable (fun u : Fˣ ↦ slice Φ g u * (((χ₁ * χ₂⁻¹) u : ℂˣ) : ℂ) *
      ((modulus (u : F) : ℝ) : ℂ) ^ (2 * s)) (multHaar F) := by sorry
