-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_mem_sumLat
-- name    : GlobalTheory.Doubling.mem_sumLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:53.134231+00:00
-- url     : https://prove2.me/theorems/76df3eaf-d453-4d6f-84c4-de700c95e9e6
-- title:
--   Doubling: mem sum Lat
-- statement:
--   The Doubling construction uses the mem sum Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L121-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L121-L123

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

theorem GlobalTheory.Doubling.mem_sumLat {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {L : Submodule O (m → X)}
    {L' : Submodule O (n → X)} {w : ι → X} :
    w ∈ sumLat e L L' ↔ (fun i => w (e (.inl i))) ∈ L ∧ (fun i => w (e (.inr i))) ∈ L' := by sorry
