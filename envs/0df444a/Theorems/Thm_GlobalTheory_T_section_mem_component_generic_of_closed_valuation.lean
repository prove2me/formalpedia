-- Prove2me | Theorems.Thm_GlobalTheory_T_section_mem_component_generic_of_closed_valuation
-- name    : GlobalTheory.T.section_mem_component_generic_of_closed_valuation
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:58:08.306127+00:00
-- url     : https://prove2.me/theorems/df560f0a-f5a3-4e24-a27d-38bd03fd6502
-- title:
--   T: section mem component generic of closed valuation
-- statement:
--   The T construction uses the section mem component generic of closed valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionMemComponentGenericOfClosedValuationStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionMemComponentGenericOfClosedValuationStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionMemComponentGenericOfClosedValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionMemComponentGenericOfClosedValuationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.section_mem_component_generic_of_closed_valuation : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (e σ : Spec (CommRingCat.of V) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → σ ≫ f = 𝟙 _ → σ (IsLocalRing.closedPoint V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → σ (⊥ : PrimeSpectrum V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by sorry
