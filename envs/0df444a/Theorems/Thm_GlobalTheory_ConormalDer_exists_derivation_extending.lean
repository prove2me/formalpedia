-- Prove2me | Theorems.Thm_GlobalTheory_ConormalDer_exists_derivation_extending
-- name    : GlobalTheory.ConormalDer.exists_derivation_extending
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:33.509582+00:00
-- url     : https://prove2.me/theorems/7a7f7b97-3196-4d01-a959-2726e22ca78d
-- title:
--   Conormal Der: exists derivation extending
-- statement:
--   The Conormal Der construction uses the exists derivation extending property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDerivationExtendingCotangentForm.lean#L92-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDerivationExtendingCotangentForm.lean#L92-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationExtendingCotangentForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.ConormalDer

theorem GlobalTheory.ConormalDer.exists_derivation_extending :
    ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) := by sorry
