-- Prove2me | Theorems.Thm_GlobalTheory_exists_tensor_idem_of_algHom
-- name    : GlobalTheory.exists_tensor_idem_of_algHom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:34.881147+00:00
-- url     : https://prove2.me/theorems/92446690-6bd0-4624-8a64-33c5515f68df
-- title:
--   Global Theory: exists tensor idem of alg Hom
-- statement:
--   The Global Theory construction uses the exists tensor idem of alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTensorIdempotentOfAlgHomToBase.lean#L6-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTensorIdempotentOfAlgHomToBase.lean#L6-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTensorIdempotentOfAlgHomToBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct Polynomial
open GlobalTheory

theorem GlobalTheory.exists_tensor_idem_of_algHom (E K E' : Type) [Field E] [CharZero E] [Field K] [Field E']
    [Algebra E K] [Algebra E E'] [FiniteDimensional E E'] (ψ : K ⊗[E] E' →ₐ[K] K) :
    ∃ e : K ⊗[E] E', ψ e = 1 ∧ ∀ a, e * a = algebraMap K (K ⊗[E] E') (ψ a) * e := by sorry
