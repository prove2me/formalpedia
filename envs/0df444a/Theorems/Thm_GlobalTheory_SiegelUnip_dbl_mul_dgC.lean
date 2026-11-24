-- Prove2me | Theorems.Thm_GlobalTheory_SiegelUnip_dbl_mul_dgC
-- name    : GlobalTheory.SiegelUnip.dbl_mul_dgC
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:11:18.481268+00:00
-- url     : https://prove2.me/theorems/f945dbef-6361-41db-b2b2-071c6e652818
-- title:
--   Siegel Unip: dbl mul dg C
-- statement:
--   The Siegel Unip construction uses the dbl mul dg C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelUnipotentAntidiagonalCorner.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelUnipotentAntidiagonalCorner.lean#L23-L25

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

theorem GlobalTheory.SiegelUnip.dbl_mul_dgC (J₀ : Matrix (Fin n) (Fin n) R) : dbl J₀ * dgC n R = adC n R * J₀ := by sorry
