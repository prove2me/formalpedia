-- Prove2me | Theorems.Thm_GlobalTheory_PerMove_bor_inv_tri
-- name    : GlobalTheory.PerMove.bor_inv_tri
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:00.605784+00:00
-- url     : https://prove2.me/theorems/71bd2f25-1e9f-4e4d-a3c7-77c7c2e5757e
-- title:
--   Per Move: bor inv tri
-- statement:
--   The Per Move construction uses the bor inv tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L155-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L155-L158

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

theorem GlobalTheory.PerMove.bor_inv_tri {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹.BlockTriangular id := by sorry
