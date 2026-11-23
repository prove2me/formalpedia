-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_exists_gl_mulVec
-- name    : GlobalTheory.BoundedBasis.exists_gl_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:17.032132+00:00
-- url     : https://prove2.me/theorems/1f0c90e7-703a-4937-816a-bf51aaef9abc
-- title:
--   Bounded Basis: exists gl mul Vec
-- statement:
--   The Bounded Basis construction uses the exists gl mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L192-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L192-L203

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

theorem GlobalTheory.BoundedBasis.exists_gl_mulVec {v w : Fin r → Fin r → E} (hv : LinearIndependent E v)
    (hw : LinearIndependent E w) : ∃ γ : GL (Fin r) E, ∀ c : Fin r → E,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (c ᵥ* Matrix.of w) = c ᵥ* Matrix.of v := by sorry
