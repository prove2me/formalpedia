-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_finrank_eq_two_mul_fdeg
-- name    : GlobalTheory.BoundedBasis.finrank_eq_two_mul_fdeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:59.329065+00:00
-- url     : https://prove2.me/theorems/f53cd3aa-cc63-4858-835f-eaab4ccce7fa
-- title:
--   Bounded Basis: finrank eq two mul fdeg
-- statement:
--   The Bounded Basis construction uses the finrank eq two mul fdeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L118-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L118-L121

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

theorem GlobalTheory.BoundedBasis.finrank_eq_two_mul_fdeg [IsCMField E] : finrank ℚ E = 2 * fdeg E := by sorry
