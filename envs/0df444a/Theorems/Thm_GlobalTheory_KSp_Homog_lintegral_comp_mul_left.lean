-- Prove2me | Theorems.Thm_GlobalTheory_KSp_Homog_lintegral_comp_mul_left
-- name    : GlobalTheory.KSp.Homog.lintegral_comp_mul_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:13.437717+00:00
-- url     : https://prove2.me/theorems/1ff20ff6-0f8e-49c8-9c62-cd194b334e2a
-- title:
--   Homog: lintegral comp mul left
-- statement:
--   The Homog construction uses the lintegral comp mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMeasureEqSmulAddHaarLocalField.lean#L102-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMeasureEqSmulAddHaarLocalField.lean#L102-L108

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.Homog
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]

theorem GlobalTheory.KSp.Homog.lintegral_comp_mul_left (μ : Measure F)
    (hμ : ∀ x : F, x ≠ 0 → μ.map (fun y ↦ x * y) = (absE x)⁻¹ • μ) {f : F → ℝ≥0∞}
    (hf : Measurable f) {x : F} (hx : x ≠ 0) :
    ∫⁻ t, f (x * t) ∂μ = (absE x)⁻¹ * ∫⁻ t, f t ∂μ := by sorry
