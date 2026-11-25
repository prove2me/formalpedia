-- Prove2me | Theorems.Thm_GlobalTheory_GaugeGermIntegral_ev_sgP
-- name    : GlobalTheory.GaugeGermIntegral.ev_sgP
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:27:53.604729+00:00
-- url     : https://prove2.me/theorems/43b837fb-cddf-4484-9a67-dd59a312734c
-- title:
--   Gauge Germ Integral: ev sg P
-- statement:
--   The Gauge Germ Integral construction uses the ev sg P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/InvariantDerivIntegral.lean#L101-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/InvariantDerivIntegral.lean#L101-L108

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantDerivIntegral
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

theorem GlobalTheory.GaugeGermIntegral.ev_sgP (Y : FBChart K V O d) (v : Fin d → K) {n : ℕ} (a : Pt K n d)
    (ha : ∀ i, constantCoeff (a i) = 0) :
    ev ![a] (Y.sgP v) = ∑ i, C (v i) * ev ![a] (sgOf K Y.h i) := by sorry
