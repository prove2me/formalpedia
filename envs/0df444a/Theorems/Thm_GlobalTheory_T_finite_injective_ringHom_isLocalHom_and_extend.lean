-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_injective_ringHom_isLocalHom_and_extend
-- name    : GlobalTheory.T.finite_injective_ringHom_isLocalHom_and_extend
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:37.776346+00:00
-- url     : https://prove2.me/theorems/628e3d6b-be12-4507-a44d-d0afc0bacc3e
-- title:
--   T: finite injective ring Hom is Local Hom and extend
-- statement:
--   The T construction uses the finite injective ring Hom is Local Hom and extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteInjectiveRingHomIsLocalHomAndExtendStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteInjectiveRingHomIsLocalHomAndExtendStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteInjectiveRingHomIsLocalHomAndExtend
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteInjectiveRingHomIsLocalHomAndExtendStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_injective_ringHom_isLocalHom_and_extend : ∀ (V R K : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [IsAlgClosed K] (ρ : V →+* R), Function.Injective ρ → ρ.Finite → IsLocalHom ρ ∧ ∀ ev : V →+* K, ∃ ev₁ : R →+* K, ev₁.comp ρ = ev := by sorry
