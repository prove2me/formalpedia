-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_mem_lieLevi
-- name    : GroundTheory.Automorphic.GodementJacquet.mem_lieLevi
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:09:49.713222+00:00
-- url     : https://prove2.me/theorems/50df0909-4eb6-53de-bb38-9e1e8a504047
-- title:
--   Godement Jacquet: mem lie Levi
-- statement:
--   The Godement Jacquet construction uses the mem lie Levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L48-L50

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
variable (F n) (β : Fin n → α)
variable {F n β}

theorem GroundTheory.Automorphic.GodementJacquet.mem_lieLevi {A : Matrix (Fin n) (Fin n) F} :
    A ∈ lieLevi F n β ↔ ∀ i j, β i ≠ β j → A i j = 0 := by sorry
