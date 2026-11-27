-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localSection_boxInd_zero_mul
-- name    : GroundTheory.Automorphic.GodementSectionLocal.localSection_boxInd_zero_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:51.461741+00:00
-- url     : https://prove2.me/theorems/96711f16-9619-5d4f-aa68-29b191709a3f
-- title:
--   Godement Section Local: local Section box Ind zero mul
-- statement:
--   The Godement Section Local construction uses the local Section box Ind zero mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L849-L867
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L849-L867

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

theorem GroundTheory.Automorphic.GodementSectionLocal.localSection_boxInd_zero_mul {χ₁ χ₂ : Fˣ →* ℂˣ} (hu₁ : IsUnramifiedChar χ₁) (s : ℂ)
    (g : GL (Fin 2) F) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    localSection χ₁ χ₂ s (boxInd F 0) (g * k) = localSection χ₁ χ₂ s (boxInd F 0) g := by sorry
