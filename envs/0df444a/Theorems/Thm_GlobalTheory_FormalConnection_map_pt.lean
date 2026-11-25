-- Prove2me | Theorems.Thm_GlobalTheory_FormalConnection_map_pt
-- name    : GlobalTheory.FormalConnection.map_pt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:32.472715+00:00
-- url     : https://prove2.me/theorems/1c36e8b5-1698-4236-800e-0cc9f49034ff
-- title:
--   Formal Connection: map pt
-- statement:
--   The Formal Connection construction uses the map pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/InvariantDerivationsCommuteFormalConnection.lean#L231-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/InvariantDerivationsCommuteFormalConnection.lean#L231-L233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.FormalLog
open GlobalTheory GlobalTheory.FormalConnection
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem GlobalTheory.FormalConnection.map_pt {n : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.map (algebraMap R k) (pt R d j i) = pt k d j i := by sorry
