-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_sum_oneValue_finrank
-- name    : GlobalTheory.CuspGL.sum_oneValue_finrank
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:07.475666+00:00
-- url     : https://prove2.me/theorems/a4ff2108-dc38-4d81-8608-8a011b259b3c
-- title:
--   Cusp GL: sum one Value finrank
-- statement:
--   The Cusp GL construction uses the sum one Value finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseOneProdIco.lean#L13-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseOneProdIco.lean#L13-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumGaussianMulProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBasesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIco
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

theorem GlobalTheory.CuspGL.sum_oneValue_finrank (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Fintype (Submodule F V)] :
    ∑ W : Submodule F V, oneValue (Nat.card F) (Module.finrank F W) = (Module.finrank F V : ℂ) := by sorry
