-- Prove2me | Theorems.Thm_GlobalTheory_T_base_change_tensor_module_compat
-- name    : GlobalTheory.T.base_change_tensor_module_compat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:47.887847+00:00
-- url     : https://prove2.me/theorems/63cbfb4f-e5f1-4ffa-90c9-4e8663b4464e
-- title:
--   T: base change tensor module compat
-- statement:
--   The T construction uses the base change tensor module compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BaseChangeTensorModuleCompatStatement.lean#L6-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BaseChangeTensorModuleCompatStatement.lean#L6-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BaseChangeTensorModuleCompat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BaseChangeTensorModuleCompatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.base_change_tensor_module_compat : ∀ (K L O : Type) [Field K] [Field L] [Algebra K L] [CommRing O] (M : Type) [AddCommGroup M]
    [Module K M] [Module O M] [SMulCommClass K O M] (N : Type) [AddCommGroup N] [Module L N] [Module O N]
    [SMulCommClass L O N] (e : L ⊗[K] M ≃ₗ[L] N), (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    letI : Module (K ⊗[ℤ] O) M := TensorProduct.Algebra.module
    letI : Module (L ⊗[ℤ] O) N := TensorProduct.Algebra.module
    ∃ _ : Algebra (K ⊗[ℤ] O) (L ⊗[ℤ] O), Module.FaithfullyFlat (K ⊗[ℤ] O) (L ⊗[ℤ] O) ∧
      Nonempty ((L ⊗[ℤ] O) ⊗[K ⊗[ℤ] O] M ≃ₗ[L ⊗[ℤ] O] N) := by sorry
