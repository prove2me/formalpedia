-- Prove2me | Theorems.Thm_GlobalTheory_isOpen_component_fibre_subtype
-- name    : GlobalTheory.isOpen_component_fibre_subtype
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:51.874567+00:00
-- url     : https://prove2.me/theorems/60088fea-6130-4af9-a5a1-6cf3e6d6a877
-- title:
--   Global Theory: is Open component fibre subtype
-- statement:
--   The Global Theory construction uses the is Open component fibre subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionMemComponentGenericOfClosedValuation.lean#L46-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionMemComponentGenericOfClosedValuation.lean#L46-L59

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

theorem GlobalTheory.isOpen_component_fibre_subtype {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (a : (f ⁻¹' {s} : Set X)) : IsOpen (connectedComponent a) := by sorry
