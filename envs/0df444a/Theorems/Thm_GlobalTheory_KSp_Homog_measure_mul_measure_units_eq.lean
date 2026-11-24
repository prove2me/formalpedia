-- Prove2me | Theorems.Thm_GlobalTheory_KSp_Homog_measure_mul_measure_units_eq
-- name    : GlobalTheory.KSp.Homog.measure_mul_measure_units_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:10.506532+00:00
-- url     : https://prove2.me/theorems/c786f1c6-0c67-4a28-b58e-c37fc8345c47
-- title:
--   Homog: measure mul measure units eq
-- statement:
--   The Homog construction uses the measure mul measure units eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMeasureEqSmulAddHaarLocalField.lean#L132-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMeasureEqSmulAddHaarLocalField.lean#L132-L210

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

theorem GlobalTheory.KSp.Homog.measure_mul_measure_units_eq (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [SFinite n]
    (hn0 : n {0} = 0) (hn : ∀ x : F, x ≠ 0 → n.map (fun y ↦ x * y) = (absE x)⁻¹ • n)
    {A : Set F} (hA : MeasurableSet A) :
    n A * lam U = n U * lam A := by sorry
