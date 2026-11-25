-- Prove2me | Theorems.Thm_GlobalTheory_GaugeGermIntegral_intS_iff
-- name    : GlobalTheory.GaugeGermIntegral.intS_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:27:39.822902+00:00
-- url     : https://prove2.me/theorems/89c96038-a99f-4c63-9531-f77f93898e27
-- title:
--   Gauge Germ Integral: int S iff
-- statement:
--   The Gauge Germ Integral construction uses the int S iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/InvariantDerivIntegral.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/InvariantDerivIntegral.lean#L25-L33

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

theorem GlobalTheory.GaugeGermIntegral.intS_iff (V : VF K) {σ : Type} (f : MvPowerSeries σ K) :
    IntS V f ↔ f ∈ Ig (intRing V) K σ := by sorry
