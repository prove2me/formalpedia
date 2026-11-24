-- Prove2me | Theorems.Thm_GlobalTheory_card_quotient_range_mulVecLin
-- name    : GlobalTheory.card_quotient_range_mulVecLin
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:46.107195+00:00
-- url     : https://prove2.me/theorems/ab4fad45-d260-4481-8704-55a71f210932
-- title:
--   Global Theory: card quotient range mul Vec Lin
-- statement:
--   The Global Theory construction uses the card quotient range mul Vec Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsRepresentativesModSimilitudeTranspose.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsRepresentativesModSimilitudeTranspose.lean#L15-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsRepresentativesModSimilitudeTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.card_quotient_range_mulVecLin {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (hA : A.det ≠ 0) :
    Nat.card ((ι → ℤ) ⧸ LinearMap.range (Matrix.toLin' A)) = A.det.natAbs := by sorry
