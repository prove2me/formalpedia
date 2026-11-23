-- Prove2me | Theorems.Thm_GlobalTheory_PerMove_det_of_triangular
-- name    : GlobalTheory.PerMove.det_of_triangular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:45.690396+00:00
-- url     : https://prove2.me/theorems/7af9ffeb-9ab5-4042-a8bf-75b27ceb2d6a
-- title:
--   Per Move: det of triangular
-- statement:
--   The Per Move construction uses the det of triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L35-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PerMove
open scoped ComplexConjugate
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate

theorem GlobalTheory.PerMove.det_of_triangular {n α : Type*} [Fintype n] [DecidableEq n] [LinearOrder α] (f : n → α)
    (hf : Function.Injective f) (M : Matrix n n ℂ) (hM : ∀ k l, f l < f k → M k l = 0) :
    M.det = ∏ k, M k k := by sorry
