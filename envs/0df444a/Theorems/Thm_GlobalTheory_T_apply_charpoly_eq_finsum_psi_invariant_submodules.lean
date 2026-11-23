-- Prove2me | Theorems.Thm_GlobalTheory_T_apply_charpoly_eq_finsum_psi_invariant_submodules
-- name    : GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:47.311998+00:00
-- url     : https://prove2.me/theorems/828ed949-9537-4b8a-be3e-38d1dfed3c30
-- title:
--   T: apply charpoly eq finsum psi invariant submodules
-- statement:
--   The T construction uses the apply charpoly eq finsum psi invariant submodules property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharpolyEqFinsumPsiStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharpolyEqFinsumPsiStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsi
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsiStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (g : Module.End F V), s (LinearMap.charpoly g) = ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2) := by sorry
