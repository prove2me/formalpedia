-- Prove2me | Theorems.Thm_GlobalTheory_ChartInv_linearPart_eq_submatrix
-- name    : GlobalTheory.ChartInv.linearPart_eq_submatrix
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:10:28.298953+00:00
-- url     : https://prove2.me/theorems/1bd7b09b-edb8-43f0-a361-7a6fc7a66d50
-- title:
--   Chart Inv: linear Part eq submatrix
-- statement:
--   The Chart Inv construction uses the linear Part eq submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalCompApplyEqMvPowerSeriesSubst.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalCompApplyEqMvPowerSeriesSubst.lean#L22-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalCompApplyEqMvPowerSeriesSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.ChartInv
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.ChartInv.linearPart_eq_submatrix (φ : Pt k 1 d) :
    GlobalTheory.FormalInv.linearPart (fun p : Fin 1 × Fin d => φ p.2) =
      (dLin φ).submatrix (Equiv.uniqueProd (Fin d) (Fin 1)) (Equiv.uniqueProd (Fin d) (Fin 1)) := by sorry
