-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_OactH_sum_smul
-- name    : GlobalTheory.FormalCalc.OactH_sum_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:56.977625+00:00
-- url     : https://prove2.me/theorems/689905ae-57fc-44f6-8584-d1a6f7d38de3
-- title:
--   Formal Calc: Oact H sum smul
-- statement:
--   The Formal Calc construction uses the Oact H sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/BetaHSumSmulRight.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/BetaHSumSmulRight.lean#L61-L66

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

theorem GlobalTheory.FormalCalc.OactH_sum_smul (B : FB R d O) (a : O) {ι : Type} (s : Finset ι) (c : ι → k)
    (v : ι → (Fin d → k) × (Fin d → k)) :
    OactH k B a (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • OactH k B a (v i) := by sorry
