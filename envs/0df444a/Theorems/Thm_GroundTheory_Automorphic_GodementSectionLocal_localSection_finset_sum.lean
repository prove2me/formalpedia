-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localSection_finset_sum
-- name    : GroundTheory.Automorphic.GodementSectionLocal.localSection_finset_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:45.169207+00:00
-- url     : https://prove2.me/theorems/cecbe4b8-3e43-5fb8-8a27-39de09385a5f
-- title:
--   Godement Section Local: local Section finset sum
-- statement:
--   The Godement Section Local construction uses the local Section finset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L503-L515
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L503-L515

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

theorem GroundTheory.Automorphic.GodementSectionLocal.localSection_finset_sum {χ₁ χ₂ : Fˣ →* ℂˣ} (h₁ : Continuous χ₁) (h₂ : Continuous χ₂)
    {s : ℂ} (hs : -quasiCharExponent (χ₁ * χ₂⁻¹) < 2 * s.re) {ι : Type*} (t : Finset ι)
    {Φ : ι → (Fin 2 → F) → ℂ} (hΦ : ∀ i ∈ t, Φ i ∈ schwartzBruhat2 F) :
    localSection χ₁ χ₂ s (∑ i ∈ t, Φ i) = ∑ i ∈ t, localSection χ₁ χ₂ s (Φ i) := by sorry
