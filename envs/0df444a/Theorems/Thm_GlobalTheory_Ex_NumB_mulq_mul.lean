-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumB_mulq_mul
-- name    : GlobalTheory.Ex.NumB.mulq_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:06:24.039348+00:00
-- url     : https://prove2.me/theorems/e5d64c33-b1f8-40ad-9e81-19ba5d399c70
-- title:
--   Num B: mulq mul
-- statement:
--   The Num B construction uses the mulq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L110-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L110-L123

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

theorem GlobalTheory.Ex.NumB.mulq_mul (a b : ℕ) (x : B.A) :
    mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) := by sorry
