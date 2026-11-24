-- Prove2me | Theorems.Thm_GlobalTheory_SiegelUnip_adR_mul_adC
-- name    : GlobalTheory.SiegelUnip.adR_mul_adC
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:11:06.34983+00:00
-- url     : https://prove2.me/theorems/ca9dfd3f-6efe-4bbb-ae7e-c1902252f1bb
-- title:
--   Siegel Unip: ad R mul ad C
-- statement:
--   The Siegel Unip construction uses the ad R mul ad C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelUnipotentAntidiagonalCorner.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelUnipotentAntidiagonalCorner.lean#L20-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelUnipotentAntidiagonalCorner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
open scoped Matrix
open GlobalTheory GlobalTheory.SiegelUnip
open Matrix
variable {R : Type} [CommRing R] {n : ℕ}

theorem GlobalTheory.SiegelUnip.adR_mul_adC : adR n R * adC n R = 2 • (1 : Matrix (Fin n) (Fin n) R) := by sorry
