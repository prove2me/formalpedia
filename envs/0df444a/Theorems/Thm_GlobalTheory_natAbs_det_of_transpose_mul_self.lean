-- Prove2me | Theorems.Thm_GlobalTheory_natAbs_det_of_transpose_mul_self
-- name    : GlobalTheory.natAbs_det_of_transpose_mul_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:12:17.223477+00:00
-- url     : https://prove2.me/theorems/58b8ea9d-e4a2-456a-bee1-079208fed645
-- title:
--   Global Theory: nat Abs det of transpose mul self
-- statement:
--   The Global Theory construction uses the nat Abs det of transpose mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsRepresentativesModSimilitudeTranspose.lean#L5-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsRepresentativesModSimilitudeTranspose.lean#L5-L13

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

theorem GlobalTheory.natAbs_det_of_transpose_mul_self (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ)
    (h : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    al.det.natAbs = m ^ 2 := by sorry
