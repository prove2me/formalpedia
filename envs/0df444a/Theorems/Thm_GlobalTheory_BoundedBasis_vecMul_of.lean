-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_vecMul_of
-- name    : GlobalTheory.BoundedBasis.vecMul_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:38.250728+00:00
-- url     : https://prove2.me/theorems/583d04fe-3a28-4e78-972d-161f822bdd8f
-- title:
--   Bounded Basis: vec Mul of
-- statement:
--   The Bounded Basis construction uses the vec Mul of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L166-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L166-L169

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.BoundedBasis.vecMul_of (c : Fin r → E) (v : Fin r → Fin r → E) :
    c ᵥ* Matrix.of v = ∑ i, c i • v i := by sorry
