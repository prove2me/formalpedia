-- Prove2me | Theorems.Thm_GlobalTheory_UU_SecMod_sum_f
-- name    : GlobalTheory.UU.SecMod.sum_f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:07.574962+00:00
-- url     : https://prove2.me/theorems/9315184b-f881-5173-92cb-ce463a8b009c
-- title:
--   Sec Mod: sum f
-- statement:
--   The Sec Mod construction uses the sum f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/FinrankComplexReal.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/FinrankComplexReal.lean#L32-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SmulOneSecEqZeroIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.UU
open GlobalTheory.UU.SecMod
variable {F : Type} [CommRing F] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of F)} {N : LB Y}

theorem GlobalTheory.UU.SecMod.sum_f {I : Type*} (S : Finset I) (s : I → SecMod p N) (j : N.ι) :
    (∑ i ∈ S, s i).sec.f j = ∑ i ∈ S, (s i).sec.f j := by sorry
