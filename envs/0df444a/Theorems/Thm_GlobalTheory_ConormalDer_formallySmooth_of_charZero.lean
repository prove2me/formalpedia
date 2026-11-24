-- Prove2me | Theorems.Thm_GlobalTheory_ConormalDer_formallySmooth_of_charZero
-- name    : GlobalTheory.ConormalDer.formallySmooth_of_charZero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:35.924677+00:00
-- url     : https://prove2.me/theorems/e1bc4e45-68db-4209-9c58-8fe6c65a10b1
-- title:
--   Conormal Der: formally Smooth of char Zero
-- statement:
--   The Conormal Der construction uses the formally Smooth of char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDerivationExtendingCotangentForm.lean#L62-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDerivationExtendingCotangentForm.lean#L62-L71

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

theorem GlobalTheory.ConormalDer.formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by sorry
