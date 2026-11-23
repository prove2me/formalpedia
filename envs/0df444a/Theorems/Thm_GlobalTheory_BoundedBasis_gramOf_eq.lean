-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_gramOf_eq
-- name    : GlobalTheory.BoundedBasis.gramOf_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:06.23177+00:00
-- url     : https://prove2.me/theorems/7b4e9055-116a-4066-8d7c-4bc53003b77b
-- title:
--   Bounded Basis: gram Of eq
-- statement:
--   The Bounded Basis construction uses the gram Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L146-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L146-L151

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

theorem GlobalTheory.BoundedBasis.gramOf_eq (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) :
    gramOf G v = Matrix.of v * G * ((Matrix.of v).map (IsCMField.complexConj E).toRingHom)ᵀ := by sorry
