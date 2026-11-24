-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_exists_comp_eq_of_ker_le
-- name    : GlobalTheory.CuspGL.exists_comp_eq_of_ker_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:30:55.851848+00:00
-- url     : https://prove2.me/theorems/d996f45d-f76b-4a77-9004-c78218d26840
-- title:
--   Cusp GL: exists comp eq of ker le
-- statement:
--   The Cusp GL construction uses the exists comp eq of ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumPrimitiveEndClassFunctionRestrictMixedSubspac.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumPrimitiveEndClassFunctionRestrictMixedSubspac.lean#L8-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspac
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

theorem GlobalTheory.CuspGL.exists_comp_eq_of_ker_le {F : Type} [Field F] {U X Y : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] (p : U →ₗ[F] X) (f : U →ₗ[F] Y)
    (h : LinearMap.ker p ≤ LinearMap.ker f) : ∃ k : X →ₗ[F] Y, ∀ u, k (p u) = f u := by sorry
