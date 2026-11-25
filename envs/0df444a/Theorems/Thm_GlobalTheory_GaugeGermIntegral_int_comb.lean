-- Prove2me | Theorems.Thm_GlobalTheory_GaugeGermIntegral_int_comb
-- name    : GlobalTheory.GaugeGermIntegral.int_comb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:27:50.205137+00:00
-- url     : https://prove2.me/theorems/7c315552-8444-4abb-aa46-9b5c15185440
-- title:
--   Gauge Germ Integral: int comb
-- statement:
--   The Gauge Germ Integral construction uses the int comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/InvariantDerivIntegral.lean#L111-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/InvariantDerivIntegral.lean#L111-L115

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantDerivIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
  ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
open GlobalTheory GlobalTheory.GaugeGermIntegral
variable {K : Type} [Field K]
variable [CharZero K] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {V : VF K}
omit [CharZero K]

theorem GlobalTheory.GaugeGermIntegral.int_comb (v : Fin d → K) (hv : ∀ i, V.Ge 0 (v i)) (f : PS K 3 d) (hf : IntS V f) :
    (∑ i, C (v i) * ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), i) f)) ∈
      Ig (intRing V) K (Fin 2 × Fin d) := by sorry
