-- Prove2me | Theorems.Thm_GlobalTheory_SW_Dict_lin_zetaOf
-- name    : GlobalTheory.SW.Dict.lin_zetaOf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:37:22.544581+00:00
-- url     : https://prove2.me/theorems/24d67653-91db-45fd-906a-9fc17ab14fbf
-- title:
--   Dict: lin zeta Of
-- statement:
--   The Dict construction uses the lin zeta Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L241-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L241-L250

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

theorem GlobalTheory.SW.Dict.lin_zetaOf (z z' : _root_.GlobalTheory.SW.CM Ψ n N)
    (k : Fin n) (m : _root_.GlobalTheory.SW.QI E N → ℂ) (hm : ∀ p, conj (m p) = m p) :
    m ⬝ᵥ _root_.GlobalTheory.SW.zetaOf Ψ z z' k =
      ∑ τ : Ψ, (_root_.GlobalTheory.SW.Dict.vec τ.1 m ⬝ᵥ z τ k +
        z' τ k ⬝ᵥ fun a => conj (_root_.GlobalTheory.SW.Dict.vec τ.1 m a)) := by sorry
