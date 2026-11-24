-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumB_cubN_inv_inv
-- name    : GlobalTheory.Ex.NumB.cubN_inv_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:06:09.542848+00:00
-- url     : https://prove2.me/theorems/52cb79af-cd5a-4e5b-bdc5-875bfaa36bca
-- title:
--   Num B: cub N inv inv
-- statement:
--   The Num B construction uses the cub N inv inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L150-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L150-L165

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

theorem GlobalTheory.Ex.NumB.cubN_inv_inv (a : ℕ) (x : B.A) :
    cubN B.θ a 1 x⁻¹ x⁻¹ * B.θ x x⁻¹ x ^ a * (B.σ x * B.σ (x ^ a)) =
      cubN B.θ a 1 x x * B.θ x⁻¹ x x⁻¹ ^ a * B.σ (x ^ a * x) := by sorry
