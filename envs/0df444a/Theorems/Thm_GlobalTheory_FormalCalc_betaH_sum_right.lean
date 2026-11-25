-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_betaH_sum_right
-- name    : GlobalTheory.FormalCalc.betaH_sum_right
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:47.749806+00:00
-- url     : https://prove2.me/theorems/8e4af24f-2cc9-4685-84da-3fa7f8cf2a57
-- title:
--   Formal Calc: beta H sum right
-- statement:
--   The Formal Calc construction uses the beta H sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/BetaHSumSmulRight.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/BetaHSumSmulRight.lean#L56-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_BetaHSumSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalCalc
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  (k : Type) [CommRing k] [Algebra R k]

theorem GlobalTheory.FormalCalc.betaH_sum_right {ι : Type} (s : Finset ι)
    (ξ : (Fin d → k) × (Fin d → k)) (v : ι → (Fin d → k) × (Fin d → k)) :
    betaH k ξ (∑ i ∈ s, v i) = ∑ i ∈ s, betaH k ξ (v i) := by sorry
