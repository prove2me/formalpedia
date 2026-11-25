-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_haarParabolic_eq_map
-- name    : GroundTheory.Automorphic.GodementJacquet.haarParabolic_eq_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:37.872904+00:00
-- url     : https://prove2.me/theorems/fe385c0d-cae4-524c-bd5f-e77b9b40875e
-- title:
--   Godement Jacquet: haar Parabolic eq map
-- statement:
--   The Godement Jacquet construction uses the haar Parabolic eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L492-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L492-L524

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

theorem GroundTheory.Automorphic.GodementJacquet.haarParabolic_eq_map (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure] :
    haarParabolic (parabolicMeasure β μ𝔪 μ𝔫) =
      map (parabolicMkHomeomorph β)
        (((haarLevi β μ𝔪).withDensity fun m => (leviRatio β m : ℝ≥0∞)).prod μ𝔫) := by sorry
