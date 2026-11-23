-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_charpoly_eq_restrict_mul_mapQ
-- name    : GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:25.661194+00:00
-- url     : https://prove2.me/theorems/b9640cfc-33d7-44c3-8b77-a214d4cece86
-- title:
--   Cusp GL: charpoly eq restrict mul map Q
-- statement:
--   The Cusp GL construction uses the charpoly eq restrict mul map Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharpolyBlockAndInvariantUnderStabilizerNilradic.lean#L10-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharpolyBlockAndInvariantUnderStabilizerNilradic.lean#L10-L34

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
open Module Module.Basis

theorem GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A) :
    LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) *
      LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) := by sorry
