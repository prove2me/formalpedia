-- Prove2me | Theorems.Thm_GlobalTheory_LowestWeight_exists_lower
-- name    : GlobalTheory.LowestWeight.exists_lower
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:19:58.826159+00:00
-- url     : https://prove2.me/theorems/b0dcb91d-b874-4580-b455-b30f138bad3a
-- title:
--   Lowest Weight: exists lower
-- statement:
--   The Lowest Weight construction uses the exists lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L72-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L72-L105

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

theorem GlobalTheory.LowestWeight.exists_lower (Y : Matrix (Fin r) (Fin r) ℂ) (hY : ∀ i, lminor Y i ≠ 0) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, (∀ a, B a a = 1) ∧ (∀ a c, c < a → B a c = 0) ∧
      ∀ a c, a < c → (Y * B) a c = 0 := by sorry
