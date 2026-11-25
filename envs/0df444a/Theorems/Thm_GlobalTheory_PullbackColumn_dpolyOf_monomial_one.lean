-- Prove2me | Theorems.Thm_GlobalTheory_PullbackColumn_dpolyOf_monomial_one
-- name    : GlobalTheory.PullbackColumn.dpolyOf_monomial_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:08.253801+00:00
-- url     : https://prove2.me/theorems/803edfca-410c-4140-9b24-954da35861ce
-- title:
--   Pullback Column: dpoly Of monomial one
-- statement:
--   The Pullback Column construction uses the dpoly Of monomial one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NabValPullbackMonomial.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NabValPullbackMonomial.lean#L24-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValPullbackMonomial
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
open GlobalTheory GlobalTheory.PullbackColumn
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.PullbackColumn.dpolyOf_monomial_one (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (mo : ι →₀ ℕ) (g : PS k 1 d) :
    DpolyOf F u (MvPolynomial.monomial mo (1 : k)) g = DmonOf F u mo g := by sorry
