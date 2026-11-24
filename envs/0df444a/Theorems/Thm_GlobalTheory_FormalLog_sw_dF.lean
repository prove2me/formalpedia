-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_sw_dF
-- name    : GlobalTheory.FormalLog.sw_dF
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:36:36.164918+00:00
-- url     : https://prove2.me/theorems/eb1ff85c-5a56-4aa3-b9f1-2edef3ee876a
-- title:
--   Formal Log: sw d F
-- statement:
--   The Formal Log construction uses the sw d F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalFamilyConstantCoeffZeroZeroSecondVar.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalFamilyConstantCoeffZeroZeroSecondVar.lean#L112-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)

theorem GlobalTheory.FormalLog.sw_dF (j b : Fin d) :
    ev (n := 2) ![pt k d 1, pt k d 0] (pderiv k ((1 : Fin 2), b) (G.F j)) = pderiv k ((0 : Fin 2), b) (G.F j) := by sorry
