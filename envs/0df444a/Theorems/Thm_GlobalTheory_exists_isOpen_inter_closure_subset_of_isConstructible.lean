-- Prove2me | Theorems.Thm_GlobalTheory_exists_isOpen_inter_closure_subset_of_isConstructible
-- name    : GlobalTheory.exists_isOpen_inter_closure_subset_of_isConstructible
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:05.644526+00:00
-- url     : https://prove2.me/theorems/fef2d09a-ea0a-4399-9b12-3392bc27021e
-- title:
--   Global Theory: exists is Open inter closure subset of is Constructible
-- statement:
--   The Global Theory construction uses the exists is Open inter closure subset of is Constructible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L33-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L33-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

theorem GlobalTheory.exists_isOpen_inter_closure_subset_of_isConstructible {f : Y → Z} (hf : Continuous f)
    {C : Set Z} (hC : IsConstructible C) :
    ∃ V : Set Y, IsOpen V ∧ V ∩ closure (f ⁻¹' C) ⊆ f ⁻¹' C ∧
      closure (V ∩ closure (f ⁻¹' C)) = closure (f ⁻¹' C) := by sorry
