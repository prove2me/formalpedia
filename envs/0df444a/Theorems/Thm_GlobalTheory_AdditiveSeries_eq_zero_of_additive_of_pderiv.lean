-- Prove2me | Theorems.Thm_GlobalTheory_AdditiveSeries_eq_zero_of_additive_of_pderiv
-- name    : GlobalTheory.AdditiveSeries.eq_zero_of_additive_of_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:31.95392+00:00
-- url     : https://prove2.me/theorems/2e19765e-b527-404e-865c-a2d5e2a692e6
-- title:
--   Additive Series: eq zero of additive of pderiv
-- statement:
--   The Additive Series construction uses the eq zero of additive of pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqZeroOfAdditiveOfPderiv.lean#L106-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqZeroOfAdditiveOfPderiv.lean#L106-L195

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqZeroOfAdditiveOfPderiv
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.AdditiveSeries
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.AdditiveSeries.eq_zero_of_additive_of_pderiv (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ)
    (G : FGLaw k d) (q : ℕ) (g : PS k (q + 1) d)
    (hadd : ev (n := q + 2) (Fin.cons (addOf G.F (pt k d 0) (pt k d 1))
        (fun j : Fin q => pt k d j.succ.succ)) g =
      ev (n := q + 2) (Fin.cons (pt k d 0) (fun j : Fin q => pt k d j.succ.succ)) g +
      ev (n := q + 2) (Fin.cons (pt k d 1) (fun j : Fin q => pt k d j.succ.succ)) g)
    (hlin : ∀ i, ev (n := q) (Fin.cons 0 (fun j : Fin q => pt k d j))
      (pderiv k ((0 : Fin (q + 1)), i) g) = 0) : g = 0 := by sorry
