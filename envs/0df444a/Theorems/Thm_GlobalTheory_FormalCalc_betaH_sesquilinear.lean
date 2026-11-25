-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_betaH_sesquilinear
-- name    : GlobalTheory.FormalCalc.betaH_sesquilinear
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:24.704962+00:00
-- url     : https://prove2.me/theorems/8f63e0d7-7fbc-5d37-991d-d7e3e093d4b1
-- title:
--   Formal Calc: beta H sesquilinear
-- statement:
--   The Formal Calc construction uses the beta H sesquilinear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/BetaHSumSmulRight.lean#L70-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/BetaHSumSmulRight.lean#L70-L100

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

theorem GlobalTheory.FormalCalc.betaH_sesquilinear : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O]
    [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O),
    (∀ (a : O) ξ η, betaH k (OactH k B a ξ) η = betaH k ξ (OactH k B (star a) η)) ∧
    (∀ (a b : O) ξ, OactH k B (a * b) ξ = OactH k B a (OactH k B b ξ)) ∧
    (∀ (a b : O) ξ, OactH k B (a + b) ξ = OactH k B a ξ + OactH k B b ξ) ∧
    (∀ ξ, OactH k B 1 ξ = ξ) ∧
    ∀ (n n' : ℕ) (c : Fin n → k) (a : Fin n → O) (c' : Fin n' → k) (a' : Fin n' → O) ξ η,
      (∑ i, c i • OactH k B (a i) ξ = ξ) → (∑ i, c' i • OactH k B (a' i) η = η) →
      (∀ ζ, ∑ i, ∑ i', (c i * c' i') • OactH k B (star (a i) * a' i') ζ = 0) →
      betaH k ξ η = 0 := by sorry
