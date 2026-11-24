-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_add_preserves_iff
-- name    : GlobalTheory.CuspGL.PrimOrth.add_preserves_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:31:56.343598+00:00
-- url     : https://prove2.me/theorems/4d06f471-3af8-46b6-b43c-1dadd59bd627
-- title:
--   Prim Orth: add preserves iff
-- statement:
--   The Prim Orth construction uses the add preserves iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiu.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiu.lean#L17-L21

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

theorem GlobalTheory.CuspGL.PrimOrth.add_preserves_iff {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A) :
    (∀ x ∈ A, (g + h) x ∈ A) ↔ ∀ x ∈ A, g x ∈ A := by sorry
