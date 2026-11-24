-- Prove2me | Theorems.Thm_GlobalTheory_EqZeroOfMemMaximalPow_eq_zero_of_mem_pow_maximal
-- name    : GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:58:17.734083+00:00
-- url     : https://prove2.me/theorems/a000ca97-62bd-4736-ac79-a52b66081cfe
-- title:
--   Eq Zero Of Mem Maximal Pow: eq zero of mem pow maximal
-- statement:
--   The Eq Zero Of Mem Maximal Pow construction uses the eq zero of mem pow maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/EqZeroOfMemPowMaximal.lean#L5-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/EqZeroOfMemPowMaximal.lean#L5-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfMemPowMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EqZeroOfMemMaximalPow

theorem GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal {R : Type} [CommRing R] [IsNoetherianRing R] (y : R)
    (h : ∀ i : MaximalSpectrum R × ℕ, y ∈ i.1.asIdeal ^ (i.2 + 1)) : y = 0 := by sorry
