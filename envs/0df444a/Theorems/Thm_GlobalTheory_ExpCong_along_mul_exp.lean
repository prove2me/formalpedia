-- Prove2me | Theorems.Thm_GlobalTheory_ExpCong_along_mul_exp
-- name    : GlobalTheory.ExpCong.along_mul_exp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:46:40.340302+00:00
-- url     : https://prove2.me/theorems/b0a7ac75-7e86-40d0-bc65-0ac7e9742398
-- title:
--   Exp Cong: along mul exp
-- statement:
--   The Exp Cong construction uses the along mul exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGroupedOfSublist.lean#L49-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGroupedOfSublist.lean#L49-L71

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

theorem GlobalTheory.ExpCong.along_mul_exp (hadd : ∀ a f g, D a (f + g) = D a f + D a g)
    (hmul : ∀ a f g, D a (f * g) = f * D a g + g * D a f) (S : Set k) (J : AddSubgroup k)
    (hSJ : ∀ s ∈ S, ∀ j ∈ J, s * j ∈ J) (hJS : ∀ j ∈ J, j ∈ S) (E φ : A) (hE : ∀ a, D a E = E * D a φ)
    (hE1 : c E = 1) (w : List ι) (f : A)
    (hf : ∀ v, v.Sublist w → c (along D v f) ∈ S) (hφ : ∀ v, v.Sublist w → c (along D v φ) ∈ J) :
    c (along D w (f * E)) - c (along D w f) ∈ J := by sorry
