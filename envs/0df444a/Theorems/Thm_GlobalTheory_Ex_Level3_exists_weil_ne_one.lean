-- Prove2me | Theorems.Thm_GlobalTheory_Ex_Level3_exists_weil_ne_one
-- name    : GlobalTheory.Ex.Level3.exists_weil_ne_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:12.853797+00:00
-- url     : https://prove2.me/theorems/49de77d3-cd8a-5c70-acc6-b4b32c81c2e9
-- title:
--   Level3: exists weil ne one
-- statement:
--   The Level3 construction uses the exists weil ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L613-L619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L613-L619

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.Level3

theorem GlobalTheory.Ex.Level3.exists_weil_ne_one : ∃ (N : NumD (ZMod 7)) (b b' : N.A), b ^ 3 = 1 ∧ b' ^ 3 = 1 ∧ N.weil 3 b b' ≠ 1 := by sorry
