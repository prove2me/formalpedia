-- Prove2me | Theorems.Thm_GlobalTheory_SW_thH_eq_thS_dictionary
-- name    : GlobalTheory.SW.thH_eq_thS_dictionary
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:12.837414+00:00
-- url     : https://prove2.me/theorems/b663bc03-4973-4886-97a0-ede167f4eb0d
-- title:
--   SW: th H eq th S dictionary
-- statement:
--   The SW construction uses the th H eq th S dictionary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L427-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L427-L433

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
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real

theorem GlobalTheory.SW.thH_eq_thS_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ), Function.Bijective (_root_.GlobalTheory.SW.ofQ : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ → Matrix (Fin n) (Fin N) E) ∧ (∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, _root_.GlobalTheory.SW.tauOf Ψ Z ∈ _root_.GlobalTheory.SW.Siegel (_root_.GlobalTheory.SW.QI E N)) ∧ (∀ ζ : Fin n → _root_.GlobalTheory.SW.QI E N → ℂ, ∃ z z' : _root_.GlobalTheory.SW.CM Ψ n N, _root_.GlobalTheory.SW.zetaOf Ψ z z' = ζ) ∧ (∀ (φ : Matrix (Fin n) (Fin N) E → ℂ) Z z z', _root_.GlobalTheory.SW.thH Ψ φ Z z z' = _root_.GlobalTheory.SW.thS (fun m => φ (_root_.GlobalTheory.SW.ofQ m)) (_root_.GlobalTheory.SW.tauOf Ψ Z) (_root_.GlobalTheory.SW.zetaOf Ψ z z')) ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.IsSB φ ↔ _root_.GlobalTheory.SW.IsSB (fun m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ => φ (_root_.GlobalTheory.SW.ofQ m)) := by sorry
