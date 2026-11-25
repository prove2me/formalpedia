-- Prove2me | Theorems.Thm_GlobalTheory_quad_round_sum
-- name    : GlobalTheory.quad_round_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:21.161243+00:00
-- url     : https://prove2.me/theorems/846e7342-05eb-4ce3-9e72-22c9101c3f8b
-- title:
--   Global Theory: quad round sum
-- statement:
--   The Global Theory construction uses the quad round sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPosZsmulMemRange.lean#L71-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPosZsmulMemRange.lean#L71-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPosZsmulMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}

theorem GlobalTheory.quad_round_sum (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    {ι : Type} [DecidableEq ι] (v : ι → X) (hv : ∀ j, 0 ≤ Q (v j)) (N : ℤ) (hN : 0 < N)
    (a : ι → ℤ) (s : Finset ι) :
    ∃ m : ι → ℤ, 4 * Q (∑ j ∈ s, (a j + N * m j) • v j) ≤ N ^ 2 * ∑ j ∈ s, Q (v j) := by sorry
