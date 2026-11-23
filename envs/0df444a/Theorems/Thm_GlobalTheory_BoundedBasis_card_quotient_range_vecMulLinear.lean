-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_card_quotient_range_vecMulLinear
-- name    : GlobalTheory.BoundedBasis.card_quotient_range_vecMulLinear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:26.216374+00:00
-- url     : https://prove2.me/theorems/5bcb8303-b9c1-4a05-afde-88f1be2c32dd
-- title:
--   Bounded Basis: card quotient range vec Mul Linear
-- statement:
--   The Bounded Basis construction uses the card quotient range vec Mul Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L79-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L79-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.BoundedBasis.card_quotient_range_vecMulLinear {r : ℕ} (N : Matrix (Fin r) (Fin r) (𝓞 E))
    (hN : N.det ≠ 0) :
    Nat.card ((Fin r → 𝓞 E) ⧸ LinearMap.range N.vecMulLinear) =
      (Algebra.norm ℤ N.det).natAbs := by sorry
