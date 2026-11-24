-- Prove2me | Theorems.Thm_GlobalTheory_DetIdeal_det_mul_vol_le
-- name    : GlobalTheory.DetIdeal.det_mul_vol_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:12.935039+00:00
-- url     : https://prove2.me/theorems/176ae7e3-3d6f-4fa8-9db2-60bcebb2cdde
-- title:
--   Det Ideal: det mul vol le
-- statement:
--   The Det Ideal construction uses the det mul vol le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean#L90-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean#L90-L119

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

theorem GlobalTheory.DetIdeal.det_mul_vol_le (c : FractionalIdeal R⁰ K) (L L' : Set (Fin r → R)) (A : Matrix (Fin r) (Fin r) K)
    (h : ∀ x ∈ L, ∀ y ∈ L', (algebraMap R K ∘ x) ⬝ᵥ A *ᵥ (algebraMap R K ∘ y) ∈ c) :
    FractionalIdeal.spanSingleton R⁰ A.det * ((vol L * vol L' : Ideal R) : FractionalIdeal R⁰ K) ≤ c ^ r := by sorry
