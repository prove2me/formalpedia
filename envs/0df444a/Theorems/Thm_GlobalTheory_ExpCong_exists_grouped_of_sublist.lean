-- Prove2me | Theorems.Thm_GlobalTheory_ExpCong_exists_grouped_of_sublist
-- name    : GlobalTheory.ExpCong.exists_grouped_of_sublist
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:46:38.822531+00:00
-- url     : https://prove2.me/theorems/3efd9e61-3ba0-4486-bda7-cb9559a2196d
-- title:
--   Exp Cong: exists grouped of sublist
-- statement:
--   The Exp Cong construction uses the exists grouped of sublist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGroupedOfSublist.lean#L79-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGroupedOfSublist.lean#L79-L97

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
variable {A k ι : Type} [CommRing A] [CommRing k] (D : ι → A → A) (c : A →+* k)

theorem GlobalTheory.ExpCong.exists_grouped_of_sublist {L : List ι} (hL : L.Nodup) (m : ι → ℕ) (v : List ι)
    (hv : v.Sublist (grouped L m)) : ∃ m' : ι → ℕ, v = grouped L m' := by sorry
