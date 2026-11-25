-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localSection_dilate
-- name    : GroundTheory.Automorphic.GodementSectionLocal.localSection_dilate
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:28.673431+00:00
-- url     : https://prove2.me/theorems/95821c07-8baa-5c10-940b-f6194efbac77
-- title:
--   Godement Section Local: local Section dilate
-- statement:
--   The Godement Section Local construction uses the local Section dilate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L517-L529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L517-L529

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

theorem GroundTheory.Automorphic.GodementSectionLocal.localSection_dilate (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Ψ : (Fin 2 → F) → ℂ) (k : ℤ) :
    localSection χ₁ χ₂ s (fun x ↦ Ψ (((unifPow (-k) : Fˣ) : F) • x)) =
      ((((χ₁ * χ₂⁻¹) (unifUnit F) : ℂˣ) : ℂ) ^ k * ((residueCard F : ℂ) ^ (-(2 * s))) ^ k) •
        localSection χ₁ χ₂ s Ψ := by sorry
