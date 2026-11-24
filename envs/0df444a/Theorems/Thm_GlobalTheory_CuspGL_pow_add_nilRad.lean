-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_pow_add_nilRad
-- name    : GlobalTheory.CuspGL.pow_add_nilRad
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:32:33.951468+00:00
-- url     : https://prove2.me/theorems/c2a4ea64-288c-452b-9e58-31ed0d7822dc
-- title:
--   Cusp GL: pow add nil Rad
-- statement:
--   The Cusp GL construction uses the pow add nil Rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/KerAevalAddStabilizerNilradicalSocle.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/KerAevalAddStabilizerNilradicalSocle.lean#L10-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_KerAevalAddStabilizerNilradicalSocle
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
variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem GlobalTheory.CuspGL.pow_add_nilRad {A : Submodule F V} {g h : Module.End F V} (hg : ∀ x ∈ A, g x ∈ A)
    (hh : h ∈ nilRad A) (n : ℕ) :
    (∀ x ∈ A, ((g + h) ^ n) x = (g ^ n) x ∧ (g ^ n) x ∈ A) ∧ ∀ x, ((g + h) ^ n) x - (g ^ n) x ∈ A := by sorry
