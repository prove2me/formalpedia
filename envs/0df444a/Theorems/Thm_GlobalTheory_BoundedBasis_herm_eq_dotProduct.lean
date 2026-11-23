-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_herm_eq_dotProduct
-- name    : GlobalTheory.BoundedBasis.herm_eq_dotProduct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:46.863612+00:00
-- url     : https://prove2.me/theorems/abf649c6-29ef-47b5-acab-bf7cc558a2df
-- title:
--   Bounded Basis: herm eq dot Product
-- statement:
--   The Bounded Basis construction uses the herm eq dot Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L137-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L137-L140

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

theorem GlobalTheory.BoundedBasis.herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = (x ᵥ* G) ⬝ᵥ fun b => cc (y b) := by sorry
