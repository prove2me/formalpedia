-- Prove2me | Theorems.Thm_GlobalTheory_T_map_mul_left_eq_inv_norm_haarChar_smul
-- name    : GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:00:40.701494+00:00
-- url     : https://prove2.me/theorems/677555a0-1c3e-443d-a6b2-2b80d3f53188
-- title:
--   T: map mul left eq inv norm haar Char smul
-- statement:
--   The T construction uses the map mul left eq inv norm haar Char smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapMulLeftEqNormSmulStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapMulLeftEqNormSmulStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMulLeftEqNormSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMulLeftEqNormSmulStatement
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

theorem GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (z : Eˣ), μ.map (fun x => (z : E) * x) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) z))⁻¹ • μ := by sorry
