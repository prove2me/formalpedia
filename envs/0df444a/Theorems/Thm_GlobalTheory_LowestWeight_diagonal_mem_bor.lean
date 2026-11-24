-- Prove2me | Theorems.Thm_GlobalTheory_LowestWeight_diagonal_mem_bor
-- name    : GlobalTheory.LowestWeight.diagonal_mem_bor
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:18:51.915808+00:00
-- url     : https://prove2.me/theorems/77cd9a8d-7e5c-4cd9-982c-6a872c6c3262
-- title:
--   Lowest Weight: diagonal mem bor
-- statement:
--   The Lowest Weight construction uses the diagonal mem bor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L155-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LowestWeightFunctionMulEq.lean#L155-L161

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem GlobalTheory.LowestWeight.diagonal_mem_bor (d : X.Ψ → Fin r → ℂ) (hd : ∀ τ a, d τ a ≠ 0) :
    (fun τ => (diagonal (d τ) : Matrix (Fin r) (Fin r) ℂ)) ∈ Bor X.Ψ r := by sorry
