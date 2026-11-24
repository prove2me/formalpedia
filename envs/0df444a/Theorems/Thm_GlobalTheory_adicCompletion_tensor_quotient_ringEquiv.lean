-- Prove2me | Theorems.Thm_GlobalTheory_adicCompletion_tensor_quotient_ringEquiv
-- name    : GlobalTheory.adicCompletion_tensor_quotient_ringEquiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:06:07.035574+00:00
-- url     : https://prove2.me/theorems/9864a2d1-e67e-4a5a-9749-da251d9a3865
-- title:
--   Global Theory: adic Completion tensor quotient ring Equiv
-- statement:
--   The Global Theory construction uses the adic Completion tensor quotient ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean#L177-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean#L177-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct

theorem GlobalTheory.adicCompletion_tensor_quotient_ringEquiv :
    ∀ (R₀ R K : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [CommRing R] [IsLocalRing R]
      [Algebra R₀ R] [CommRing K] [Algebra R K] [Algebra R₀ K] [IsScalarTower R₀ R K],
      Function.Surjective (algebraMap R₀ R) →
        Nonempty (AdicCompletion (maximalIdeal R) R ⊗[R] K ≃+*
          AdicCompletion (maximalIdeal R₀) R₀ ⊗[R₀] K) := by sorry
