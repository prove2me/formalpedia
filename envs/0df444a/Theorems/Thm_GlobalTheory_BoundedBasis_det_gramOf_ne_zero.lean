-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_det_gramOf_ne_zero
-- name    : GlobalTheory.BoundedBasis.det_gramOf_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:21.13779+00:00
-- url     : https://prove2.me/theorems/f9bbd670-fe96-4057-abf6-205b7200c508
-- title:
--   Bounded Basis: det gram Of ne zero
-- statement:
--   The Bounded Basis construction uses the det gram Of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L159-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L159-L163

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

theorem GlobalTheory.BoundedBasis.det_gramOf_ne_zero {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    {v : Fin r → Fin r → E} (hv : LinearIndependent E v) : (gramOf G v).det ≠ 0 := by sorry
