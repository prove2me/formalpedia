-- Prove2me | Theorems.Thm_GlobalTheory_SiegelUnip_adR_tr
-- name    : GlobalTheory.SiegelUnip.adR_tr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:11:11.00244+00:00
-- url     : https://prove2.me/theorems/72d9f2fc-6297-4746-a25d-1217cfc48621
-- title:
--   Siegel Unip: ad R tr
-- statement:
--   The Siegel Unip construction uses the ad R tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelUnipotentAntidiagonalCorner.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelUnipotentAntidiagonalCorner.lean#L34-L35

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

theorem GlobalTheory.SiegelUnip.adR_tr : (adR n R)ᵀ = adC n R := by sorry
