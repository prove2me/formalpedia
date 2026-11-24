-- Prove2me | Theorems.Thm_GlobalTheory_SiegelUnip_dgC_map
-- name    : GlobalTheory.SiegelUnip.dgC_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:11:22.165067+00:00
-- url     : https://prove2.me/theorems/5d400645-a35e-4ed9-9507-115945cf13de
-- title:
--   Siegel Unip: dg C map
-- statement:
--   The Siegel Unip construction uses the dg C map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelUnipotentAntidiagonalCorner.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelUnipotentAntidiagonalCorner.lean#L37-L38

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

theorem GlobalTheory.SiegelUnip.dgC_map {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) : (dgC n R).map c = dgC n R := by sorry
