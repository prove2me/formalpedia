-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localSection_borelElt_mul
-- name    : GroundTheory.Automorphic.GodementSectionLocal.localSection_borelElt_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:01.122965+00:00
-- url     : https://prove2.me/theorems/11939828-f213-5973-bec2-2b9e98bed1ad
-- title:
--   Godement Section Local: local Section borel Elt mul
-- statement:
--   The Godement Section Local construction uses the local Section borel Elt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L156-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L156-L172

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

theorem GroundTheory.Automorphic.GodementSectionLocal.localSection_borelElt_mul (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Φ : (Fin 2 → F) → ℂ) (a d : Fˣ)
    (x : F) (g : GL (Fin 2) F) :
    localSection χ₁ χ₂ s Φ (borelElt a d x * g) =
      (χ₁ a : ℂ) * (χ₂ d : ℂ) * modPow (a : F) s * modPow (d : F) (-s) *
        localSection χ₁ χ₂ s Φ g := by sorry
