-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_formalGroupLaw_ev_x_zero
-- name    : GlobalTheory.FormalLog.formalGroupLaw_ev_x_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:00:11.943435+00:00
-- url     : https://prove2.me/theorems/572bccf2-2e29-49dd-997e-efdcc3160eda
-- title:
--   Formal Log: formal Group Law ev x zero
-- statement:
--   The Formal Log construction uses the formal Group Law ev x zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalEvSecondPointOfXZero.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalEvSecondPointOfXZero.lean#L35-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
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

theorem GlobalTheory.FormalLog.formalGroupLaw_ev_x_zero (i : Fin d) : ev (n := 1) ![pt k d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by sorry
