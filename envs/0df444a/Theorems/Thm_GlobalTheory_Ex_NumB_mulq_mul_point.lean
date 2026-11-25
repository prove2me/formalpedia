-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumB_mulq_mul_point
-- name    : GlobalTheory.Ex.NumB.mulq_mul_point
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:20:39.661834+00:00
-- url     : https://prove2.me/theorems/2a7bca9a-966d-4898-8cc4-d712b1f16ad0
-- title:
--   Num B: mulq mul point
-- statement:
--   The Num B construction uses the mulq mul point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L125-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L125-L148

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
open GlobalTheory.Ex.NumB
variable {O : Type} [CommRing O] (B : NumB O)

theorem GlobalTheory.Ex.NumB.mulq_mul_point (a : ℕ) (x y : B.A) :
    mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y *
      (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) := by sorry
