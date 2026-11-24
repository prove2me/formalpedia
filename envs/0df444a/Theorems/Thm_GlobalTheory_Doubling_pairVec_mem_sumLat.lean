-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_pairVec_mem_sumLat
-- name    : GlobalTheory.Doubling.pairVec_mem_sumLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:16.340349+00:00
-- url     : https://prove2.me/theorems/1d6b2373-de9b-4a10-bf41-60a17a473fe5
-- title:
--   Doubling: pair Vec mem sum Lat
-- statement:
--   The Doubling construction uses the pair Vec mem sum Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L125-L127

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : m ⊕ n ≃ ι)
variable [Fintype m] [Fintype n] [Fintype ι]
variable [DecidableEq m] [DecidableEq n] [DecidableEq ι]
omit [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι]

theorem GlobalTheory.Doubling.pairVec_mem_sumLat {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {L : Submodule O (m → X)}
    {L' : Submodule O (n → X)} {x : m → X} {y : n → X} : pairVec e x y ∈ sumLat e L L' ↔ x ∈ L ∧ y ∈ L' := by sorry
