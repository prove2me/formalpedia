-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_finrank_eq_zero_of_irreducible_charpoly
-- name    : GlobalTheory.CuspGL.finrank_eq_zero_of_irreducible_charpoly
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:32:17.13396+00:00
-- url     : https://prove2.me/theorems/6b9f5569-3b3f-4e6e-821c-8a9f760498ee
-- title:
--   Cusp GL: finrank eq zero of irreducible charpoly
-- statement:
--   The Cusp GL construction uses the finrank eq zero of irreducible charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseCharpolyOfIrreduci.lean#L33-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseCharpolyOfIrreduci.lean#L33-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyOfIrreduci
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

theorem GlobalTheory.CuspGL.finrank_eq_zero_of_irreducible_charpoly {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (g : Module.End F V) (hg : Irreducible (LinearMap.charpoly g))
    (W : Submodule F V) (hne : W ≠ ⊤) (hW : ∀ x ∈ W, g x ∈ W) : Module.finrank F W = 0 := by sorry
