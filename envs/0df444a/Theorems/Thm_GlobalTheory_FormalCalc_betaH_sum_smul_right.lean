-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_betaH_sum_smul_right
-- name    : GlobalTheory.FormalCalc.betaH_sum_smul_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:55.098835+00:00
-- url     : https://prove2.me/theorems/c060c8f7-b973-4c7e-a1b9-bcbfa55c953f
-- title:
--   Formal Calc: beta H sum smul right
-- statement:
--   The Formal Calc construction uses the beta H sum smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/BetaHSumSmulRight.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/BetaHSumSmulRight.lean#L49-L54

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

theorem GlobalTheory.FormalCalc.betaH_sum_smul_right {ι : Type} (s : Finset ι) (c : ι → k)
    (ξ : (Fin d → k) × (Fin d → k)) (v : ι → (Fin d → k) × (Fin d → k)) :
    betaH k ξ (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i * betaH k ξ (v i) := by sorry
