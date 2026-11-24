-- Prove2me | Theorems.Thm_GlobalTheory_KSp_map_mul_left_eq_norm_smul
-- name    : GlobalTheory.KSp.map_mul_left_eq_norm_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:48:40.896117+00:00
-- url     : https://prove2.me/theorems/100f2924-0b65-4be9-9c8b-21e704ea6cf2
-- title:
--   KSp: map mul left eq norm smul
-- statement:
--   The KSp construction uses the map mul left eq norm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapMulLeftEqNormSmul.lean#L12-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapMulLeftEqNormSmul.lean#L12-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapLinearEquivAddHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMulLeftEqNormSmul
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
open GlobalTheory GlobalTheory.KSp

theorem GlobalTheory.KSp.map_mul_left_eq_norm_smul (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (z : Eˣ) :
    μ.map (fun x => (z : E) * x) =
      (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) z))⁻¹ • μ := by sorry
