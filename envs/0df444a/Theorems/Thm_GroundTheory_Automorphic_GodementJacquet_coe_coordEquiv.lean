-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_coe_coordEquiv
-- name    : GroundTheory.Automorphic.GodementJacquet.coe_coordEquiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:59.938806+00:00
-- url     : https://prove2.me/theorems/5cee66bd-8888-49ff-b356-91ff20d9a944
-- title:
--   Godement Jacquet: coe coord Equiv
-- statement:
--   The Godement Jacquet construction uses the coe coord Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L310-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L310-L310

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJParabolicFubini
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Measure Topology Set
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α]
variable (β : Fin n → α)

theorem GroundTheory.Automorphic.GodementJacquet.coe_coordEquiv : ⇑(coordEquiv (F := F) β) = coordAddEquiv β := by sorry
