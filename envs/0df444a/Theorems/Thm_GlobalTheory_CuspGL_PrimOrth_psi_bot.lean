-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_psi_bot
-- name    : GlobalTheory.CuspGL.PrimOrth.psi_bot
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:31:33.280912+00:00
-- url     : https://prove2.me/theorems/dc573032-b95c-424d-a338-0980056a03b1
-- title:
--   Prim Orth: psi bot
-- statement:
--   The Prim Orth construction uses the psi bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiu.lean#L77-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiu.lean#L77-L88

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

theorem GlobalTheory.CuspGL.PrimOrth.psi_bot {s : F[X] → ℂ} (hs : IsAdditive s) (U : Type) [AddCommGroup U] [Module F U]
    [FiniteDimensional F U] [Subsingleton U] (g : Module.End F U) : psi s U g = 0 := by sorry
