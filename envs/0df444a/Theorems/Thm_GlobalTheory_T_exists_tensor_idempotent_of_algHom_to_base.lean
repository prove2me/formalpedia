-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_tensor_idempotent_of_algHom_to_base
-- name    : GlobalTheory.T.exists_tensor_idempotent_of_algHom_to_base
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:37:46.157072+00:00
-- url     : https://prove2.me/theorems/8b63cc44-d625-43be-86bb-87564cf92a7c
-- title:
--   T: exists tensor idempotent of alg Hom to base
-- statement:
--   The T construction uses the exists tensor idempotent of alg Hom to base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTensorIdempotentOfAlgHomToBaseStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTensorIdempotentOfAlgHomToBaseStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTensorIdempotentOfAlgHomToBase
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTensorIdempotentOfAlgHomToBaseStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_tensor_idempotent_of_algHom_to_base : ∀ (E K E' : Type) [Field E] [CharZero E] [Field K] [Field E'] [Algebra E K] [Algebra E E'] [FiniteDimensional E E'] (ψ : K ⊗[E] E' →ₐ[K] K), ∃ e : K ⊗[E] E', ψ e = 1 ∧ ∀ a, e * a = algebraMap K (K ⊗[E] E') (ψ a) * e := by sorry
