-- Prove2me | Theorems.Thm_GlobalTheory_HkLocal_analyticOrderNatAt_comp_affine
-- name    : GlobalTheory.HkLocal.analyticOrderNatAt_comp_affine
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:36:34.190138+00:00
-- url     : https://prove2.me/theorems/1e9fc307-34f6-419c-a5cd-bd007c89e99b
-- title:
--   Hk Local: analytic Order Nat At comp affine
-- statement:
--   The Hk Local construction uses the analytic Order Nat At comp affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionLogDerivLocalFormula.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionLogDerivLocalFormula.lean#L11-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.HkLocal

theorem GlobalTheory.HkLocal.analyticOrderNatAt_comp_affine (g : ℂ → ℂ) (c ρ w : ℂ) (hρ : ρ ≠ 0) :
    analyticOrderNatAt (fun z => g (c + ρ * z)) w = analyticOrderNatAt g (c + ρ * w) := by sorry
