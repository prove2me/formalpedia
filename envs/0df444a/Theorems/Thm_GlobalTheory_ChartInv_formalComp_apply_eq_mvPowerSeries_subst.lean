-- Prove2me | Theorems.Thm_GlobalTheory_ChartInv_formalComp_apply_eq_mvPowerSeries_subst
-- name    : GlobalTheory.ChartInv.formalComp_apply_eq_mvPowerSeries_subst
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:10:01.810382+00:00
-- url     : https://prove2.me/theorems/34777499-ae78-454b-82e8-e49829f0a6d4
-- title:
--   Chart Inv: formal Comp apply eq mv Power Series subst
-- statement:
--   The Chart Inv construction uses the formal Comp apply eq mv Power Series subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalCompApplyEqMvPowerSeriesSubst.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalCompApplyEqMvPowerSeriesSubst.lean#L13-L20

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

theorem GlobalTheory.ChartInv.formalComp_apply_eq_mvPowerSeries_subst (φ ψ : Pt k 1 d) (i : Fin d) :
    comp1 φ ψ i = (φ i).subst (fun p : Fin 1 × Fin d => ψ p.2) := by sorry
