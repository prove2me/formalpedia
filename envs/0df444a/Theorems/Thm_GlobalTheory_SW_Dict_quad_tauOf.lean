-- Prove2me | Theorems.Thm_GlobalTheory_SW_Dict_quad_tauOf
-- name    : GlobalTheory.SW.Dict.quad_tauOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:34.563469+00:00
-- url     : https://prove2.me/theorems/9b2a1051-9222-4211-a009-4e5d4d2d96e3
-- title:
--   Dict: quad tau Of
-- statement:
--   The Dict construction uses the quad tau Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L203-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L203-L235

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

theorem GlobalTheory.SW.Dict.quad_tauOf (Z : _root_.GlobalTheory.SW.CM Ψ N N)
    (m : _root_.GlobalTheory.SW.QI E N → ℂ) (hm : ∀ p, conj (m p) = m p) :
    m ⬝ᵥ _root_.GlobalTheory.SW.tauOf Ψ Z *ᵥ m =
      2 * ∑ τ : Ψ, _root_.GlobalTheory.SW.Dict.vec τ.1 m ⬝ᵥ Z τ *ᵥ
        fun a => conj (_root_.GlobalTheory.SW.Dict.vec τ.1 m a) := by sorry
