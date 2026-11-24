-- Prove2me | Theorems.Thm_GlobalTheory_AdicPackage_adicCompletion_package
-- name    : GlobalTheory.AdicPackage.adicCompletion_package
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:55:17.682126+00:00
-- url     : https://prove2.me/theorems/ac563142-ce0a-4ca8-b3e5-5cf1412d27a9
-- title:
--   Adic Package: adic Completion package
-- statement:
--   The Adic Package construction uses the adic Completion package property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdicCompletionNoetherianFlatComplete.lean#L6-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdicCompletionNoetherianFlatComplete.lean#L6-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdicCompletionNoetherianFlatComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdicPackage

theorem GlobalTheory.AdicPackage.adicCompletion_package : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I : Ideal B),
    ∃ (C : Type) (_ : CommRing C) (φ : B →+* C), IsNoetherianRing C ∧ φ.Flat ∧
      IsAdicComplete (I.map φ) C ∧ ∀ (m : ℕ) (a : Ideal B), I ^ m ≤ a → (a.map φ).comap φ = a := by sorry
