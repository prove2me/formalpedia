-- Prove2me | Theorems.Thm_GlobalTheory_HalfIdentity_dpolyOf_monomial
-- name    : GlobalTheory.HalfIdentity.dpolyOf_monomial
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:02:31.246251+00:00
-- url     : https://prove2.me/theorems/57dfaef9-bb6d-4315-9e0e-551a55c6402e
-- title:
--   Half Identity: dpoly Of monomial
-- statement:
--   The Half Identity construction uses the dpoly Of monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/SecondOrderMonomial.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/SecondOrderMonomial.lean#L39-L43

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

theorem GlobalTheory.HalfIdentity.dpolyOf_monomial (m : ι →₀ ℕ) (a : k) (f : PS k 1 d) :
    DpolyOf F u (MvPolynomial.monomial m a) f = C a * DmonOf F u m f := by sorry
