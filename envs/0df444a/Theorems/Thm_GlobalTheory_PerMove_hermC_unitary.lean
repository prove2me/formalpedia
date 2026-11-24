-- Prove2me | Theorems.Thm_GlobalTheory_PerMove_hermC_unitary
-- name    : GlobalTheory.PerMove.hermC_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:03.534169+00:00
-- url     : https://prove2.me/theorems/c204b5d6-271a-48b1-8674-915ec1f39c4b
-- title:
--   Per Move: herm C unitary
-- statement:
--   The Per Move construction uses the herm C unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L79-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L79-L94

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

theorem GlobalTheory.PerMove.hermC_unitary (τ : E →+* ℂ) (G γ : Matrix (Fin r) (Fin r) E)
    (hγ : ∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (γ *ᵥ u) (γ *ᵥ v) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G u v) (u w : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (γ.map τ *ᵥ u) (γ.map τ *ᵥ w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u w := by sorry
