-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_vecMul_borelElt
-- name    : GroundTheory.Automorphic.GodementSectionLocal.vecMul_borelElt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:16.424641+00:00
-- url     : https://prove2.me/theorems/737eb8ca-617b-49ca-bdcc-6b2e4c39a85e
-- title:
--   Godement Section Local: vec Mul borel Elt
-- statement:
--   The Godement Section Local construction uses the vec Mul borel Elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L92-L95

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

theorem GroundTheory.Automorphic.GodementSectionLocal.vecMul_borelElt (a d : Fˣ) (x t : F) :
    ![0, t] ᵥ* (borelElt a d x : Matrix (Fin 2) (Fin 2) F) = ![0, t * d] := by sorry
