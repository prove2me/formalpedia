-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_det_borelElt
-- name    : GroundTheory.Automorphic.GodementSectionLocal.det_borelElt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:54.076453+00:00
-- url     : https://prove2.me/theorems/255a94ec-f0db-5efd-873a-3f8e590fbeaa
-- title:
--   Godement Section Local: det borel Elt
-- statement:
--   The Godement Section Local construction uses the det borel Elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L87-L90

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

theorem GroundTheory.Automorphic.GodementSectionLocal.det_borelElt (a d : Fˣ) (x : F) :
    Matrix.GeneralLinearGroup.det (borelElt a d x) = a * d := by sorry
