-- Prove2me | Theorems.Thm_GlobalTheory_SiegelUnip_dgC_tr_dbl_dgC
-- name    : GlobalTheory.SiegelUnip.dgC_tr_dbl_dgC
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:11:34.91808+00:00
-- url     : https://prove2.me/theorems/c047d730-5248-4e72-808b-dc01bcd770dd
-- title:
--   Siegel Unip: dg C tr dbl dg C
-- statement:
--   The Siegel Unip construction uses the dg C tr dbl dg C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelUnipotentAntidiagonalCorner.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelUnipotentAntidiagonalCorner.lean#L31-L32

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

theorem GlobalTheory.SiegelUnip.dgC_tr_dbl_dgC (J₀ : Matrix (Fin n) (Fin n) R) : (dgC n R)ᵀ * dbl J₀ * dgC n R = 0 := by sorry
