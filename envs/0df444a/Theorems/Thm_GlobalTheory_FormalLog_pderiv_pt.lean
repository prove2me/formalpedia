-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_pderiv_pt
-- name    : GlobalTheory.FormalLog.pderiv_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:36.882172+00:00
-- url     : https://prove2.me/theorems/d386eba9-a4d6-4579-ad9e-2597c8e38897
-- title:
--   Formal Log: pderiv pt
-- statement:
--   The Formal Log construction uses the pderiv pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalEvSecondPointOfXZero.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalEvSecondPointOfXZero.lean#L51-L55

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

theorem GlobalTheory.FormalLog.pderiv_pt {n : ℕ} (v : Fin n × Fin d) (j : Fin n) (i : Fin d) :
    pderiv k v (pt k (n := n) d j i) = if (j, i) = v then 1 else 0 := by sorry
