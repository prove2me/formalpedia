-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_integral_parabolic_integralGL
-- name    : GroundTheory.Automorphic.Measures.integral_parabolic_integralGL
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:08:51.232321+00:00
-- url     : https://prove2.me/theorems/d9932db1-d657-459c-9582-483e02130188
-- title:
--   Measures: integral parabolic integral GL
-- statement:
--   The Measures construction uses the integral parabolic integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Measures.lean#L313-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Measures.lean#L313-L323

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] {β : Fin n → α}
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

theorem GroundTheory.Automorphic.Measures.integral_parabolic_integralGL (hβ : Monotone β) (μG : Measure (GL (Fin n) F))
    [μG.IsHaarMeasure] (μP : Measure (Iwasawa.blockUpper F n β)) [μP.IsHaarMeasure]
    (μK : Measure (GLnLocal.integralGL F n)) [μK.IsHaarMeasure] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : GL (Fin n) F → E}
    (hf : Integrable f μG) :
    μG.real (GLnLocal.integralGL F n) • ∫ p, ∫ k, f ((p : GL (Fin n) F) * k) ∂μK ∂μP =
      (μP.real (Subtype.val ⁻¹' (GLnLocal.integralGL F n : Set (GL (Fin n) F))) * μK.real univ) •
        ∫ g, f g ∂μG := by sorry
