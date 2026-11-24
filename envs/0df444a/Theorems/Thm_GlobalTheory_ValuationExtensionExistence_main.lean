-- Prove2me | Theorems.Thm_GlobalTheory_ValuationExtensionExistence_main
-- name    : GlobalTheory.ValuationExtensionExistence.main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:50:31.553837+00:00
-- url     : https://prove2.me/theorems/d545f71e-f68c-415a-ad46-44a74520ad8c
-- title:
--   Valuation Extension Existence: main
-- statement:
--   The Valuation Extension Existence construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsFurtherLast.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsFurtherLast.lean#L32-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ValuationExtensionExistence

theorem GlobalTheory.ValuationExtensionExistence.main : ∀ (V R K : Type) [inst : CommRing V] [IsDomain V] [IsLocalRing V]
    [inst_3 : CommRing R] [IsDomain R] [IsLocalRing R] [inst_6 : Field K] [IsAlgClosed K]
    (ρ : V →+* R), Function.Injective (⇑ρ : V → R) → RingHom.Finite ρ →
      IsLocalHom ρ ∧ ∀ (ev : V →+* K), ∃ (ev₁ : R →+* K), RingHom.comp ev₁ ρ = ev := by sorry
