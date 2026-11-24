-- Prove2me | Theorems.Thm_GlobalTheory_LocalNorm_exists_eq_sq_add_of_notMem
-- name    : GlobalTheory.LocalNorm.exists_eq_sq_add_of_notMem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:14:21.351695+00:00
-- url     : https://prove2.me/theorems/0e5ee460-577d-4449-85ce-bc27658fd231
-- title:
--   Local Norm: exists eq sq add of not Mem
-- statement:
--   The Local Norm construction uses the exists eq sq add of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsBinaryEqAdicCompletion.lean#L295-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsBinaryEqAdicCompletion.lean#L295-L338

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.LocalNorm.exists_eq_sq_add_of_notMem (H : Host E)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    {u : 𝓞 (maximalRealSubfield E)} (hu : u ∉ v.asIdeal) :
    ∃ a b : v.adicCompletion (maximalRealSubfield E),
      algebraMap (maximalRealSubfield E) _ (u : maximalRealSubfield E) = a ^ 2 + H.d * b ^ 2 := by sorry
