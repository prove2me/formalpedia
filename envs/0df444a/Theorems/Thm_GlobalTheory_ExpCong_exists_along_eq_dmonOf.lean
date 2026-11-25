-- Prove2me | Theorems.Thm_GlobalTheory_ExpCong_exists_along_eq_dmonOf
-- name    : GlobalTheory.ExpCong.exists_along_eq_dmonOf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:44:30.491865+00:00
-- url     : https://prove2.me/theorems/893e514d-188b-475c-8154-ffdf9483bbbd
-- title:
--   Exp Cong: exists along eq dmon Of
-- statement:
--   The Exp Cong construction uses the exists along eq dmon Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGroupedOfSublist.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGroupedOfSublist.lean#L122-L128

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
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
open GlobalTheory GlobalTheory.ExpCong
variable {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)

theorem GlobalTheory.ExpCong.exists_along_eq_dmonOf (m : ι →₀ ℕ) (v : List ι)
    (hv : v.Sublist (grouped (Finset.univ : Finset ι).toList m).reverse) :
    ∃ m' : ι →₀ ℕ, ∀ f : PS k 1 d, along (fun l => Dof F (u l)) v f = DmonOf F u m' f := by sorry
