-- Prove2me | Theorems.Thm_GlobalTheory_LocalNorm_exists_mul_eq_of_mem_mul_map
-- name    : GlobalTheory.LocalNorm.exists_mul_eq_of_mem_mul_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:16:52.774327+00:00
-- url     : https://prove2.me/theorems/7a09a2e1-1e06-4f18-a990-8362057688c7
-- title:
--   Local Norm: exists mul eq of mem mul map
-- statement:
--   The Local Norm construction uses the exists mul eq of mem mul map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsBinaryEqAdicCompletion.lean#L141-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsBinaryEqAdicCompletion.lean#L141-L151

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
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
open GlobalTheory GlobalTheory.LocalNorm

theorem GlobalTheory.LocalNorm.exists_mul_eq_of_mem_mul_map {B : Type*} [CommRing B] (σ : B →+* B) {I : Ideal B}
    {i r m : B} (h : Ideal.span {r} * I ≤ Ideal.span {i}) (hm : m ∈ I * I.map σ) :
    ∃ c, c * (i * σ i) = r * σ r * m := by sorry
