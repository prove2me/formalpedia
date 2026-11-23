-- Prove2me | Theorems.Thm_GlobalTheory_DetIdeal_prod_mem_pow
-- name    : GlobalTheory.DetIdeal.prod_mem_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:17.296711+00:00
-- url     : https://prove2.me/theorems/c74af0d1-20e7-4c5c-ba5b-c59675f16abe
-- title:
--   Det Ideal: prod mem pow
-- statement:
--   The Det Ideal construction uses the prod mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean#L40-L47

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

theorem GlobalTheory.DetIdeal.prod_mem_pow {ι : Type} (c : FractionalIdeal R⁰ K) (s : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ s, f i ∈ c) : ∏ i ∈ s, f i ∈ c ^ s.card := by sorry
