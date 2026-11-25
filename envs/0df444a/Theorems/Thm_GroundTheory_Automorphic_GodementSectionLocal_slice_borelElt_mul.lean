-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_slice_borelElt_mul
-- name    : GroundTheory.Automorphic.GodementSectionLocal.slice_borelElt_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:43:14.496797+00:00
-- url     : https://prove2.me/theorems/271e8e68-4537-43f1-b6af-d1a69f39a5df
-- title:
--   Godement Section Local: slice borel Elt mul
-- statement:
--   The Godement Section Local construction uses the slice borel Elt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GodementSectionLocal.lean#L151-L154

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

theorem GroundTheory.Automorphic.GodementSectionLocal.slice_borelElt_mul (Φ : (Fin 2 → F) → ℂ) (a d : Fˣ) (x : F) (g : GL (Fin 2) F) :
    slice Φ (borelElt a d x * g) = fun t ↦ slice Φ g (t * d) := by sorry
