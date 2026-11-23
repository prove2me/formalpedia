-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_isPrimitive_psi
-- name    : GlobalTheory.CuspGL.isPrimitive_psi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:10.392933+00:00
-- url     : https://prove2.me/theorems/1771de67-81b7-493b-bec8-5393624d5e9c
-- title:
--   Cusp GL: is Primitive psi
-- statement:
--   The Cusp GL construction uses the is Primitive psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveEndClassFunctionInvariantSubspaceMobi.lean#L188-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveEndClassFunctionInvariantSubspaceMobi.lean#L188-L199

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
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.isPrimitive_psi : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → IsPrimitive (psi s V) := by sorry
