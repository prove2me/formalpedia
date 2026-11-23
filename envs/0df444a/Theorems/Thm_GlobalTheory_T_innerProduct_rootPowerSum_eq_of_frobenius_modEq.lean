-- Prove2me | Theorems.Thm_GlobalTheory_T_innerProduct_rootPowerSum_eq_of_frobenius_modEq
-- name    : GlobalTheory.T.innerProduct_rootPowerSum_eq_of_frobenius_modEq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:19.327525+00:00
-- url     : https://prove2.me/theorems/1ca7a98a-5da8-4ed1-bd6a-079b4fb48846
-- title:
--   T: inner Product root Power Sum eq of frobenius mod Eq
-- statement:
--   The T construction uses the inner Product root Power Sum eq of frobenius mod Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InnerProductRootPowerSumEqOfFrobeniusModEqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InnerProductRootPowerSumEqOfFrobeniusModEqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEqStatement
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

theorem GlobalTheory.T.innerProduct_rootPowerSum_eq_of_frobenius_modEq : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ k l i : ℕ, k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)] → ipGL φ (fun g : Module.End F V => rootSum θ k (LinearMap.charpoly g)) = ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) := by sorry
