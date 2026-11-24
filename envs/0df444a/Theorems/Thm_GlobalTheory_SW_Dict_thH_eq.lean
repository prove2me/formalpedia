-- Prove2me | Theorems.Thm_GlobalTheory_SW_Dict_thH_eq
-- name    : GlobalTheory.SW.Dict.thH_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:38:49.32912+00:00
-- url     : https://prove2.me/theorems/04147e2d-99b4-413b-87b8-b1d05b44e57e
-- title:
--   Dict: th H eq
-- statement:
--   The Dict construction uses the th H eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L269-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L269-L295

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
variable (Ψ : Finset (E →+* ℂ))
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable (Ψ : Finset (E →+* ℂ))

theorem GlobalTheory.SW.Dict.thH_eq (φ : Matrix (Fin n) (Fin N) E → ℂ)
    (Z : _root_.GlobalTheory.SW.CM Ψ N N) (z z' : _root_.GlobalTheory.SW.CM Ψ n N) :
    _root_.GlobalTheory.SW.thH Ψ φ Z z z' =
      _root_.GlobalTheory.SW.thS (fun m => φ (_root_.GlobalTheory.SW.ofQ m))
        (_root_.GlobalTheory.SW.tauOf Ψ Z) (_root_.GlobalTheory.SW.zetaOf Ψ z z') := by sorry
