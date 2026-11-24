-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_invariantSubspaceMobiusInverseRec_eq_of_finrank_lt
-- name    : GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_eq_of_finrank_lt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:32:59.058802+00:00
-- url     : https://prove2.me/theorems/16aeba29-79db-446d-84ff-72557c7ec690
-- title:
--   Cusp GL: invariant Subspace Mobius Inverse Rec eq of finrank lt
-- statement:
--   The Cusp GL construction uses the invariant Subspace Mobius Inverse Rec eq of finrank lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean#L39-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]

theorem GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_eq_of_finrank_lt (s : F[X] → ℂ) (n : ℕ) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (g : Module.End F V), Module.finrank F V < n → Module.finrank F V < m →
    invariantSubspaceMobiusInverseRec s n V g = invariantSubspaceMobiusInverseRec s m V g := by sorry
