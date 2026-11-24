-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_isUnit_add_iff
-- name    : GlobalTheory.CuspGL.PrimOrth.isUnit_add_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:31:24.38393+00:00
-- url     : https://prove2.me/theorems/97bafddc-db69-40de-a095-e67c199b4369
-- title:
--   Prim Orth: is Unit add iff
-- statement:
--   The Prim Orth construction uses the is Unit add iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiu.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiu.lean#L42-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.PrimOrth
variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem GlobalTheory.CuspGL.PrimOrth.isUnit_add_iff [FiniteDimensional F V] {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) : IsUnit (g + h) ↔ IsUnit g := by sorry
