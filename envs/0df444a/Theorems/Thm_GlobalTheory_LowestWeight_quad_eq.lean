-- Prove2me | Theorems.Thm_GlobalTheory_LowestWeight_quad_eq
-- name    : GlobalTheory.LowestWeight.quad_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:19:48.042419+00:00
-- url     : https://prove2.me/theorems/571bba22-3598-4b37-9bef-185564c6a47c
-- title:
--   Lowest Weight: quad eq
-- statement:
--   The Lowest Weight construction uses the quad eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L18-L34

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

theorem GlobalTheory.LowestWeight.quad_eq {p : ℕ} (e : Fin p → Fin r) (s : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
    (v : Fin p → ℂ) :
    star v ⬝ᵥ ((Yᵀ * diagonal (fun a => (s a : ℂ)) * Y.map (starRingEnd ℂ)).submatrix e e *ᵥ v) =
      ((∑ k, s k * ‖∑ a, Y k (e a) * conj (v a)‖ ^ 2 : ℝ) : ℂ) := by sorry
