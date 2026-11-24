-- Prove2me | Theorems.Thm_GlobalTheory_separated_of_isOpen_component_subtype
-- name    : GlobalTheory.separated_of_isOpen_component_subtype
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:20:24.457098+00:00
-- url     : https://prove2.me/theorems/bc78962f-cebc-4278-bf60-d5db2af9d17f
-- title:
--   Global Theory: separated of is Open component subtype
-- statement:
--   The Global Theory construction uses the separated of is Open component subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionMemComponentGenericOfClosedValuation.lean#L10-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionMemComponentGenericOfClosedValuation.lean#L10-L44

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

theorem GlobalTheory.separated_of_isOpen_component_subtype {X : Type*} [TopologicalSpace X] (F : Set X) (a : X)
    (ha : a ∈ F) (ho : IsOpen (connectedComponent (⟨a, ha⟩ : F))) :
    Disjoint (connectedComponentIn F a) (closure (F \ connectedComponentIn F a)) ∧
      Disjoint (closure (connectedComponentIn F a)) (F \ connectedComponentIn F a) := by sorry
