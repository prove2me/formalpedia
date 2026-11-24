-- Prove2me | Theorems.Thm_GlobalTheory_Ex_mulq_add
-- name    : GlobalTheory.Ex.mulq_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:06:21.663658+00:00
-- url     : https://prove2.me/theorems/7ed25d32-15d9-4e36-81bc-6beaae180f19
-- title:
--   Ex: mulq add
-- statement:
--   The Ex construction uses the mulq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L45-L58

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

theorem GlobalTheory.Ex.mulq_add (h : IsCub θ) (σ : A → U) (m n : ℕ) (x : A) :
    mulq θ σ (m + n) x * dbl θ σ x ^ (m * n) =
      mulq θ σ m x * mulq θ σ n x * (cubN θ m 1 x (x ^ n) * cubN θ n 1 x x ^ m) := by sorry
