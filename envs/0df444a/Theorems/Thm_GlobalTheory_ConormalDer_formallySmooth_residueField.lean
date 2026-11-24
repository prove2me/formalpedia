-- Prove2me | Theorems.Thm_GlobalTheory_ConormalDer_formallySmooth_residueField
-- name    : GlobalTheory.ConormalDer.formallySmooth_residueField
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:42.601701+00:00
-- url     : https://prove2.me/theorems/6c52b00c-d42c-4720-b6a3-0caef9c3831e
-- title:
--   Conormal Der: formally Smooth residue Field
-- statement:
--   The Conormal Der construction uses the formally Smooth residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDerivationExtendingCotangentForm.lean#L73-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDerivationExtendingCotangentForm.lean#L73-L90

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

theorem GlobalTheory.ConormalDer.formallySmooth_residueField (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R]
    [CommRing B] [IsLocalRing B] [Algebra R B]
    (hu : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) :
    Algebra.FormallySmooth R (ResidueField B) := by sorry
