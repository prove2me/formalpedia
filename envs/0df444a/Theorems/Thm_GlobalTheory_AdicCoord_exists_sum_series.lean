-- Prove2me | Theorems.Thm_GlobalTheory_AdicCoord_exists_sum_series
-- name    : GlobalTheory.AdicCoord.exists_sum_series
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:57:04.836282+00:00
-- url     : https://prove2.me/theorems/686c553a-6a33-46ad-bb73-1b819b8df131
-- title:
--   Adic Coord: exists sum series
-- statement:
--   The Adic Coord construction uses the exists sum series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAdicCoordinatesOfBasisModP.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAdicCoordinatesOfBasisModP.lean#L11-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAdicCoordinatesOfBasisModP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdicCoord

theorem GlobalTheory.AdicCoord.exists_sum_series {R : Type} [CommRing R] (x : R)
    [IsPrecomplete (Ideal.span {x}) R] (a : ℕ → R) :
    ∃ L : R, ∀ N : ℕ, x ^ N ∣ (∑ k ∈ Finset.range N, x ^ k * a k) - L := by sorry
