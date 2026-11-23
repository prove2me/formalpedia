-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_herm_vecMul_left
-- name    : GlobalTheory.BoundedBasis.herm_vecMul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:49.541399+00:00
-- url     : https://prove2.me/theorems/0ddcc803-7a5d-4a7f-8823-0c6204cf5d1b
-- title:
--   Bounded Basis: herm vec Mul left
-- statement:
--   The Bounded Basis construction uses the herm vec Mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L171-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L171-L174

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

theorem GlobalTheory.BoundedBasis.herm_vecMul_left (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (c : Fin r → E)
    (k : Fin r) : herm G (c ᵥ* Matrix.of v) (v k) = (c ᵥ* gramOf G v) k := by sorry
