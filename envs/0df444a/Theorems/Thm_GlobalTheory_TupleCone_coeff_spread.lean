-- Prove2me | Theorems.Thm_GlobalTheory_TupleCone_coeff_spread
-- name    : GlobalTheory.TupleCone.coeff_spread
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:11.705389+00:00
-- url     : https://prove2.me/theorems/b5a28c2e-57a3-57da-90db-6f77d96765c7
-- title:
--   Tuple Cone: coeff spread
-- statement:
--   The Tuple Cone construction uses the coeff spread property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L152-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L152-L161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}

theorem GlobalTheory.TupleCone.coeff_spread {L : Type*} [CommRing L] (p : L[X]) (n : ℕ) :
    (spread L p).coeff n = C (p.coeff n) * X ^ n := by sorry
