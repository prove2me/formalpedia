-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_PsiPrimitive_step
-- name    : GlobalTheory.CuspGL.PsiPrimitive.step
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:32:03.796927+00:00
-- url     : https://prove2.me/theorems/659b9565-b139-4864-86c3-e142b6bd709e
-- title:
--   Psi Primitive: step
-- statement:
--   The Psi Primitive construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveEndClassFunctionInvariantSubspaceMobi.lean#L62-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveEndClassFunctionInvariantSubspaceMobi.lean#L62-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspacStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyTransversalSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.PsiPrimitive

theorem GlobalTheory.CuspGL.PsiPrimitive.step {F : Type} [Field F] [Finite F] (s : F[X] → ℂ) (hs : IsAdditive s) (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ih : ∀ W : Submodule F V, W ≠ ⊤ → IsPrimitive (psi s W)) : IsPrimitive (psi s V) := by sorry
