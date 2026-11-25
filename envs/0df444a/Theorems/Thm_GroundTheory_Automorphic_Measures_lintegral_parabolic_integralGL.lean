-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_lintegral_parabolic_integralGL
-- name    : GroundTheory.Automorphic.Measures.lintegral_parabolic_integralGL
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:08:52.457183+00:00
-- url     : https://prove2.me/theorems/75f01c86-a40d-5b56-b523-7b9d6b28b69b
-- title:
--   Measures: lintegral parabolic integral GL
-- statement:
--   The Measures construction uses the lintegral parabolic integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Measures.lean#L291-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Measures.lean#L291-L300

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

theorem GroundTheory.Automorphic.Measures.lintegral_parabolic_integralGL (hβ : Monotone β) (μG : Measure (GL (Fin n) F))
    [μG.IsHaarMeasure] (μP : Measure (Iwasawa.blockUpper F n β)) [μP.IsHaarMeasure]
    (μK : Measure (GLnLocal.integralGL F n)) [μK.IsHaarMeasure] {f : GL (Fin n) F → ℝ≥0∞}
    (hf : Measurable f) :
    μG (GLnLocal.integralGL F n) * ∫⁻ p, ∫⁻ k, f ((p : GL (Fin n) F) * k) ∂μK ∂μP =
      μP (Subtype.val ⁻¹' (GLnLocal.integralGL F n : Set (GL (Fin n) F))) * μK univ *
        ∫⁻ g, f g ∂μG := by sorry
