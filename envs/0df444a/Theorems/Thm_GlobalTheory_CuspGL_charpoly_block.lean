-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_charpoly_block
-- name    : GlobalTheory.CuspGL.charpoly_block
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:06.690822+00:00
-- url     : https://prove2.me/theorems/cc2b6464-2ace-4a96-bed8-8cb316c19381
-- title:
--   Cusp GL: charpoly block
-- statement:
--   The Cusp GL construction uses the charpoly block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharpolyBlockAndInvariantUnderStabilizerNilradic.lean#L36-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharpolyBlockAndInvariantUnderStabilizerNilradic.lean#L36-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.charpoly_block : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A),
    LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) *
      LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) ∧
    ∀ h ∈ nilRad A, LinearMap.charpoly (g + h) = LinearMap.charpoly g := by sorry
