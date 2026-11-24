-- Prove2me | Theorems.Thm_GlobalTheory_LocalNorm_exists_binary_eq_adicCompletion
-- name    : GlobalTheory.LocalNorm.exists_binary_eq_adicCompletion
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:14:14.121771+00:00
-- url     : https://prove2.me/theorems/cfb6a279-affc-4fbf-9291-feee90ac8ae8
-- title:
--   Local Norm: exists binary eq adic Completion
-- statement:
--   The Local Norm construction uses the exists binary eq adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsBinaryEqAdicCompletion.lean#L42-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsBinaryEqAdicCompletion.lean#L42-L95

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

theorem GlobalTheory.LocalNorm.exists_binary_eq_adicCompletion {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {a n u : 𝓞 F}
    (hD : a ^ 2 - 4 * n ∉ v.asIdeal) (hu : u ∉ v.asIdeal) :
    ∃ r s : v.adicCompletion F, r ^ 2 + algebraMap F _ (a : F) * r * s
      + algebraMap F _ (n : F) * s ^ 2 = algebraMap F _ (u : F) := by sorry
