-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_comap_parabolicMeasure
-- name    : GroundTheory.Automorphic.GodementJacquet.comap_parabolicMeasure
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:31:25.386984+00:00
-- url     : https://prove2.me/theorems/4ae0f1ed-a15e-53fa-9242-1d8b8e3af9a6
-- title:
--   Godement Jacquet: comap parabolic Measure
-- statement:
--   The Godement Jacquet construction uses the comap parabolic Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L430-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L430-L473

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
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]
variable {β : Fin n → α}

theorem GroundTheory.Automorphic.GodementJacquet.comap_parabolicMeasure (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure] :
    (parabolicMeasure β μ𝔪 μ𝔫).comap (parabolicChart F n β).toFun =
      map (parabolicMkHomeomorph β) ((μ𝔪.comap (leviChart β).toFun).prod μ𝔫) := by sorry
