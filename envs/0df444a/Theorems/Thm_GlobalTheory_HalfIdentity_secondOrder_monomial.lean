-- Prove2me | Theorems.Thm_GlobalTheory_HalfIdentity_secondOrder_monomial
-- name    : GlobalTheory.HalfIdentity.secondOrder_monomial
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:02:05.650494+00:00
-- url     : https://prove2.me/theorems/b5069966-a50d-47b3-be82-207d767c5d13
-- title:
--   Half Identity: second Order monomial
-- statement:
--   The Half Identity construction uses the second Order monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/SecondOrderMonomial.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/SecondOrderMonomial.lean#L49-L58

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

theorem GlobalTheory.HalfIdentity.secondOrder_monomial (c : ι → ι → k) (m : ι →₀ ℕ) (a : k) :
    secondOrder k c (MvPolynomial.monomial m a) =
      ∑ x, ∑ y, MvPolynomial.monomial (m - Finsupp.single y 1 - Finsupp.single x 1)
        (a * (c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k))) := by sorry
