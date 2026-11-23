-- Prove2me | Theorems.Thm_GlobalTheory_SW_Dict_sum_type
-- name    : GlobalTheory.SW.Dict.sum_type
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:17.199676+00:00
-- url     : https://prove2.me/theorems/d72303ed-f9de-4c7b-a8ac-1ea4ebbf6ac4
-- title:
--   Dict: sum type
-- statement:
--   The Dict construction uses the sum type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L172-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L172-L192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

theorem GlobalTheory.SW.Dict.sum_type {Ψ : Finset (E →+* ℂ)}
    (hΨ : _root_.GlobalTheory.SW.IsType Ψ) (f : (E →+* ℂ) → ℂ) :
    ∑ σ, f σ = ∑ τ : Ψ, (f τ + f (ComplexEmbedding.conjugate τ.1)) := by sorry
