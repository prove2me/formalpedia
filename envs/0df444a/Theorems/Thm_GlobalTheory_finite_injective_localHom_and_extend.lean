-- Prove2me | Theorems.Thm_GlobalTheory_finite_injective_localHom_and_extend
-- name    : GlobalTheory.finite_injective_localHom_and_extend
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:46:33.718804+00:00
-- url     : https://prove2.me/theorems/88be447a-d457-4774-ad07-9f7fcb236764
-- title:
--   Global Theory: finite injective local Hom and extend
-- statement:
--   The Global Theory construction uses the finite injective local Hom and extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteInjectiveRingHomIsLocalHomAndExtend.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteInjectiveRingHomIsLocalHomAndExtend.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteInjectiveRingHomIsLocalHomAndExtend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.finite_injective_localHom_and_extend (V R K : Type) [CommRing V] [IsDomain V] [IsLocalRing V]
    [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [IsAlgClosed K] (ρ : V →+* R) :
    Function.Injective ρ → ρ.Finite → IsLocalHom ρ ∧ ∀ ev : V →+* K, ∃ ev₁ : R →+* K, ev₁.comp ρ = ev := by sorry
