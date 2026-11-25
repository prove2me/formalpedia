-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_betaH_OactH
-- name    : GlobalTheory.FormalCalc.betaH_OactH
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:36.958187+00:00
-- url     : https://prove2.me/theorems/6bc10eb4-25c0-4435-9e2a-b01bc543fef6
-- title:
--   Formal Calc: beta H Oact H
-- statement:
--   The Formal Calc construction uses the beta H Oact H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/BetaHSumSmulRight.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/BetaHSumSmulRight.lean#L33-L36

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

theorem GlobalTheory.FormalCalc.betaH_OactH (B : FB R d O) (a : O) (ξ η : (Fin d → k) × (Fin d → k)) :
    betaH k (OactH k B a ξ) η = betaH k ξ (OactH k B (star a) η) := by sorry
