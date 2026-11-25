-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_borelElt_val
-- name    : GroundTheory.Automorphic.GodementSectionLocal.borelElt_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:55.30837+00:00
-- url     : https://prove2.me/theorems/ddd320d3-1ae2-5c2c-bf95-1ac98fcf988e
-- title:
--   Godement Section Local: borel Elt val
-- statement:
--   The Godement Section Local construction uses the borel Elt val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L84-L85

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

theorem GroundTheory.Automorphic.GodementSectionLocal.borelElt_val (a d : Fˣ) (x : F) :
    (borelElt a d x : Matrix (Fin 2) (Fin 2) F) = !![(a : F), x; 0, (d : F)] := by sorry
