-- Prove2me | Theorems.Thm_GlobalTheory_GaugeGermIntegral_second_deriv
-- name    : GlobalTheory.GaugeGermIntegral.second_deriv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:43.616266+00:00
-- url     : https://prove2.me/theorems/7936e84d-e196-4331-92fd-854aaca66ad1
-- title:
--   Gauge Germ Integral: second deriv
-- statement:
--   The Gauge Germ Integral construction uses the second deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/InvariantDerivIntegral.lean#L47-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/InvariantDerivIntegral.lean#L47-L97

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
open GlobalTheory.GaugeSecondDeriv

theorem GlobalTheory.GaugeGermIntegral.second_deriv (B : FB K d O) (h : PS K 2 d) (hc : B.IsCanonGauge K h) (b : Fin d) :
    ∑ j, ev (n := 2) ![pt K d 1, 0] (pderiv K ((1 : Fin 2), b) (B.G.F j)) *
        pderiv K ((1 : Fin 2), j) h =
      ev (n := 2) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), b) h) -
        ev (n := 2) ![pt K d 0, pt K d 1, 0] (pderiv K ((2 : Fin 3), b) B.ph2) := by sorry
