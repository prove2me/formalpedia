-- Prove2me | Theorems.Thm_GlobalTheory_DetIdeal_det_mul_vol_eq
-- name    : GlobalTheory.DetIdeal.det_mul_vol_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:20.946286+00:00
-- url     : https://prove2.me/theorems/7e64c6f0-305f-4452-aa2e-fcb267602119
-- title:
--   Det Ideal: det mul vol eq
-- statement:
--   The Det Ideal construction uses the det mul vol eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean#L121-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean#L121-L192

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DetIdeal
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}

theorem GlobalTheory.DetIdeal.det_mul_vol_eq (c : FractionalIdeal R⁰ K) (hc : c ≠ 0) (L L' : Set (Fin r → R))
    (A : Matrix (Fin r) (Fin r) K) (hA : A.det ≠ 0) (hL' : vol L' ≠ ⊥)
    (h : ∀ v : Fin r → K, (∀ y ∈ L', v ⬝ᵥ A *ᵥ (algebraMap R K ∘ y) ∈ c) ↔ ∃ x ∈ L, algebraMap R K ∘ x = v) :
    FractionalIdeal.spanSingleton R⁰ A.det * ((vol L * vol L' : Ideal R) : FractionalIdeal R⁰ K) = c ^ r := by sorry
