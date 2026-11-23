-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_neg_mem_nilRad
-- name    : GlobalTheory.CuspGL.PrimOrth.neg_mem_nilRad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:07.703006+00:00
-- url     : https://prove2.me/theorems/ea257ae9-5025-4946-b18b-f3cd854ca48e
-- title:
--   Prim Orth: neg mem nil Rad
-- statement:
--   The Prim Orth construction uses the neg mem nil Rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiu.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiu.lean#L10-L11

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

theorem GlobalTheory.CuspGL.PrimOrth.neg_mem_nilRad {A : Submodule F V} {h : Module.End F V} (hh : h ∈ nilRad A) : -h ∈ nilRad A := by sorry
