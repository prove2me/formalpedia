-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_betaH_sum_smul_left
-- name    : GlobalTheory.FormalCalc.betaH_sum_smul_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:40.246685+00:00
-- url     : https://prove2.me/theorems/e97ac10f-dffb-4368-ab25-4d5a9517f3f0
-- title:
--   Formal Calc: beta H sum smul left
-- statement:
--   The Formal Calc construction uses the beta H sum smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/BetaHSumSmulRight.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/BetaHSumSmulRight.lean#L42-L47

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

theorem GlobalTheory.FormalCalc.betaH_sum_smul_left {ι : Type} (s : Finset ι) (c : ι → k)
    (v : ι → (Fin d → k) × (Fin d → k)) (η : (Fin d → k) × (Fin d → k)) :
    betaH k (∑ i ∈ s, c i • v i) η = ∑ i ∈ s, c i * betaH k (v i) η := by sorry
