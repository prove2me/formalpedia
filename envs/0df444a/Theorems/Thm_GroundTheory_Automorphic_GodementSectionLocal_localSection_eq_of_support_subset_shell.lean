-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localSection_eq_of_support_subset_shell
-- name    : GroundTheory.Automorphic.GodementSectionLocal.localSection_eq_of_support_subset_shell
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:47.844436+00:00
-- url     : https://prove2.me/theorems/a3aff0e0-a0c1-4281-9e22-0ee9bfa0964d
-- title:
--   Godement Section Local: local Section eq of support subset shell
-- statement:
--   The Godement Section Local construction uses the local Section eq of support subset shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L779-L795
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L779-L795

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

theorem GroundTheory.Automorphic.GodementSectionLocal.localSection_eq_of_support_subset_shell (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ)
    {Ψ : (Fin 2 → F) → ℂ} (hΨ : Function.support Ψ ⊆ shell F) {k : GL (Fin 2) F}
    (hk : k ∈ GLnLocal.integralGL F 2) :
    localSection χ₁ χ₂ s Ψ k = (χ₁ (detU k) : ℂ) *
      ∫ u, slice Ψ k u * (((χ₁ * χ₂⁻¹) u : ℂˣ) : ℂ) ∂multHaar F := by sorry
