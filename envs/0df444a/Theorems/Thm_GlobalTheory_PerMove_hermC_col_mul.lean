-- Prove2me | Theorems.Thm_GlobalTheory_PerMove_hermC_col_mul
-- name    : GlobalTheory.PerMove.hermC_col_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:50.041477+00:00
-- url     : https://prove2.me/theorems/8f615fb9-94d0-438d-8a61-8d9d42637e65
-- title:
--   Per Move: herm C col mul
-- statement:
--   The Per Move construction uses the herm C col mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L120-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L120-L129

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.PerMove.hermC_col_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x b : Matrix (Fin r) (Fin r) ℂ)
    (a : Fin r) (w : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (x * b) a) w = ∑ c, b c a * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x c) w := by sorry
