-- Prove2me | Theorems.Thm_GlobalTheory_LowestWeight_signed_isHermitian
-- name    : GlobalTheory.LowestWeight.signed_isHermitian
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:20:03.594105+00:00
-- url     : https://prove2.me/theorems/9efc5673-3e6b-4717-a781-6254a2710cb7
-- title:
--   Lowest Weight: signed is Hermitian
-- statement:
--   The Lowest Weight construction uses the signed is Hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L36-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder
open GlobalTheory.LowestWeight
variable {r : ℕ}

theorem GlobalTheory.LowestWeight.signed_isHermitian (s : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ) :
    (Yᵀ * diagonal (fun a => (s a : ℂ)) * Y.map (starRingEnd ℂ)).IsHermitian := by sorry
