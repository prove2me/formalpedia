-- Prove2me | Theorems.Thm_GlobalTheory_HalfIdentity_secondOrder_add
-- name    : GlobalTheory.HalfIdentity.secondOrder_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:02:04.328281+00:00
-- url     : https://prove2.me/theorems/8a4c63c6-e2cc-4f92-a0e7-19402b168d61
-- title:
--   Half Identity: second Order add
-- statement:
--   The Half Identity construction uses the second Order add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/SecondOrderMonomial.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/SecondOrderMonomial.lean#L45-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_SecondOrderMonomial
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.HalfIdentity
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)
variable [Fintype ι]

theorem GlobalTheory.HalfIdentity.secondOrder_add (c : ι → ι → k) (P Q : MvPolynomial ι k) :
    secondOrder k c (P + Q) = secondOrder k c P + secondOrder k c Q := by sorry
