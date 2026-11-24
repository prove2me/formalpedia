-- Prove2me | Theorems.Thm_GlobalTheory_T_primitiveClassFunction_expansion_rootSums
-- name    : GlobalTheory.T.primitiveClassFunction_expansion_rootSums
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:41:01.845803+00:00
-- url     : https://prove2.me/theorems/5d632d20-e1d8-455a-bad2-fd7537e87d2f
-- title:
--   T: primitive Class Function expansion root Sums
-- statement:
--   The T construction uses the primitive Class Function expansion root Sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveClassFunctionExpansionRootSumsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveClassFunctionExpansionRootSumsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveClassFunctionExpansionRootSums
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveClassFunctionExpansionRootSumsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.primitiveClassFunction_expansion_rootSums : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ g : Module.End F V, IsUnit g → glCard F (Module.finrank F V) * (Module.finrank F V : ℂ) * φ g = ∑ k ∈ Finset.range (Nat.card F ^ Module.finrank F V - 1), ipGL φ (fun g : Module.End F V => rootSum θ k (LinearMap.charpoly g)) * psi (rootSum θ k) V g := by sorry
