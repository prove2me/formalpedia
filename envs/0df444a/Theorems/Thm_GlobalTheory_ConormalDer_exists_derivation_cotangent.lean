-- Prove2me | Theorems.Thm_GlobalTheory_ConormalDer_exists_derivation_cotangent
-- name    : GlobalTheory.ConormalDer.exists_derivation_cotangent
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:35.477018+00:00
-- url     : https://prove2.me/theorems/bd98abe9-96ac-457d-83ad-aea3c926f5b7
-- title:
--   Conormal Der: exists derivation cotangent
-- statement:
--   The Conormal Der construction uses the exists derivation cotangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDerivationExtendingCotangentForm.lean#L7-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDerivationExtendingCotangentForm.lean#L7-L60

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

theorem GlobalTheory.ConormalDer.exists_derivation_cotangent (R B : Type) [CommRing R] [CommRing B] [IsLocalRing B]
    [Algebra R B] [Algebra.FormallySmooth R (ResidueField B)] :
    ∃ D : B →ₗ[R] CotangentSpace B, (∀ a b, D (a * b) = a • D b + b • D a) ∧
      ∀ t : maximalIdeal B, D t = (maximalIdeal B).toCotangent t := by sorry
