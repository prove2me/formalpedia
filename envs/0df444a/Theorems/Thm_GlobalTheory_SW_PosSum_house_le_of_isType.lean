-- Prove2me | Theorems.Thm_GlobalTheory_SW_PosSum_house_le_of_isType
-- name    : GlobalTheory.SW.PosSum.house_le_of_isType
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:44:35.269063+00:00
-- url     : https://prove2.me/theorems/d3f40326-023f-4c12-be20-48e6fc71b022
-- title:
--   Pos Sum: house le of is Type
-- statement:
--   The Pos Sum construction uses the house le of is Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableExpNegTraceTotallyPositiveHermitian.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableExpNegTraceTotallyPositiveHermitian.lean#L46-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.PosSum

theorem GlobalTheory.SW.PosSum.house_le_of_isType {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {x : E} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ τ ∈ Ψ, ‖τ x‖ ≤ B) : house x ≤ B := by sorry
