-- Prove2me | Theorems.Thm_GlobalTheory_Ex_cubN_mul_point
-- name    : GlobalTheory.Ex.cubN_mul_point
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:07:10.31135+00:00
-- url     : https://prove2.me/theorems/e244ea8b-1b3b-4761-b84d-9376345d4a1a
-- title:
--   Ex: cub N mul point
-- statement:
--   The Ex construction uses the cub N mul point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L28-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem GlobalTheory.Ex.cubN_mul_point (h : IsCub θ) (a : ℕ) (x y z : A) :
    cubN θ a 1 (x * y) z * θ x y z ^ a = cubN θ a 1 x z * cubN θ a 1 y z * θ (x ^ a) (y ^ a) z := by sorry
