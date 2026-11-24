-- Prove2me | Theorems.Thm_GlobalTheory_T_homogeneousMeasure_eq_smul_addHaar_localField
-- name    : GlobalTheory.T.homogeneousMeasure_eq_smul_addHaar_localField
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:18.779881+00:00
-- url     : https://prove2.me/theorems/d93b5ef3-ca99-4040-a6d3-963b36407ae7
-- title:
--   T: homogeneous Measure eq smul add Haar local Field
-- statement:
--   The T construction uses the homogeneous Measure eq smul add Haar local Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMeasureEqSmulAddHaarLocalFieldStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMeasureEqSmulAddHaarLocalFieldStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalFieldStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.homogeneousMeasure_eq_smul_addHaar_localField : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [IsFiniteMeasureOnCompacts n], n {0} = 0 → (∀ u : Fˣ, n.map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n) → ∃ r : NNReal, n = r • lam := by sorry
