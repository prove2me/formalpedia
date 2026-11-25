-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_integral_haarParabolic
-- name    : GroundTheory.Automorphic.GodementJacquet.integral_haarParabolic
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:04.051385+00:00
-- url     : https://prove2.me/theorems/ae35081a-b64b-4a97-a381-fa8dec0f7c11
-- title:
--   Godement Jacquet: integral haar Parabolic
-- statement:
--   The Godement Jacquet construction uses the integral haar Parabolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L540-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L540-L558

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

theorem GroundTheory.Automorphic.GodementJacquet.integral_haarParabolic (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure]
    {H : blockUpper F n β → ℂ} (hH : Integrable H (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))) :
    ∫ p, H p ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) =
      ∫ m, (leviRatio β m : ℂ) * ∫ u, H (parabolicMk β m u) ∂μ𝔫 ∂(haarLevi β μ𝔪) := by sorry
