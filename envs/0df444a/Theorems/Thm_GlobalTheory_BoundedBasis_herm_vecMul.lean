-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_herm_vecMul
-- name    : GlobalTheory.BoundedBasis.herm_vecMul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:39.805505+00:00
-- url     : https://prove2.me/theorems/2cfbfd67-b589-4c11-9f6d-7f9e58a7dc83
-- title:
--   Bounded Basis: herm vec Mul
-- statement:
--   The Bounded Basis construction uses the herm vec Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L176-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L176-L182

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

theorem GlobalTheory.BoundedBasis.herm_vecMul (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (c d : Fin r → E) :
    herm G (c ᵥ* Matrix.of v) (d ᵥ* Matrix.of v) = herm (gramOf G v) c d := by sorry
