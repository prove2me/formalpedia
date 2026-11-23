-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_invariantSubspaceMobiusInverseRec_succ
-- name    : GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:53.801649+00:00
-- url     : https://prove2.me/theorems/dbb61a52-0c95-4ed5-a202-6cc0f39a14ea
-- title:
--   Cusp GL: invariant Subspace Mobius Inverse Rec succ
-- statement:
--   The Cusp GL construction uses the invariant Subspace Mobius Inverse Rec succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean#L31-L33

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

theorem GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ (s : F[X] → ℂ) (n : ℕ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g : Module.End F V) : invariantSubspaceMobiusInverseRec s (n + 1) V g = s (LinearMap.charpoly g) -
      ∑ᶠ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}, invariantSubspaceMobiusInverseRec s n W.1 (g.restrict W.2.2) := by sorry
