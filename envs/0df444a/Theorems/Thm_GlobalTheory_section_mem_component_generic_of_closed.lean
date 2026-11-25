-- Prove2me | Theorems.Thm_GlobalTheory_section_mem_component_generic_of_closed
-- name    : GlobalTheory.section_mem_component_generic_of_closed
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:28.850841+00:00
-- url     : https://prove2.me/theorems/9787fa69-e8c4-4d49-bc9c-bc9f8be1da2f
-- title:
--   Global Theory: section mem component generic of closed
-- statement:
--   The Global Theory construction uses the section mem component generic of closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionMemComponentGenericOfClosedValuation.lean#L61-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionMemComponentGenericOfClosedValuation.lean#L61-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothGenericFibreClosurePartitionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionMemComponentGenericOfClosedValuation
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
open GlobalTheory

theorem GlobalTheory.section_mem_component_generic_of_closed :
    ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (e σ : Spec (CommRingCat.of V) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → σ ≫ f = 𝟙 _ → σ (IsLocalRing.closedPoint V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → σ (⊥ : PrimeSpectrum V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by sorry
