-- Prove2me | Theorems.Thm_GlobalTheory_interior_frontier_preimage_of_isConstructible
-- name    : GlobalTheory.interior_frontier_preimage_of_isConstructible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:31.495799+00:00
-- url     : https://prove2.me/theorems/3cdd6f58-f64e-44e3-ba4f-0e64aa05e62c
-- title:
--   Global Theory: interior frontier preimage of is Constructible
-- statement:
--   The Global Theory construction uses the interior frontier preimage of is Constructible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L11-L25

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

theorem GlobalTheory.interior_frontier_preimage_of_isConstructible {f : Y → Z} (hf : Continuous f)
    {C : Set Z} (hC : IsConstructible C) : interior (frontier (f ⁻¹' C)) = ∅ := by sorry
