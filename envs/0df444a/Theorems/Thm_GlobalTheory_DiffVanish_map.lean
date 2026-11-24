-- Prove2me | Theorems.Thm_GlobalTheory_DiffVanish_map
-- name    : GlobalTheory.DiffVanish.map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:17.17085+00:00
-- url     : https://prove2.me/theorems/f6ffb8c2-932e-4e33-9a09-7cce6a1d1b1f
-- title:
--   Diff Vanish: map
-- statement:
--   The Diff Vanish construction uses the map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L193-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L193-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]

theorem GlobalTheory.DiffVanish.map {N : Type*} [AddCommGroup N] {n : ℕ} {φ : G → M} (h : DiffVanish n φ)
    (f : M →+ N) : DiffVanish n (f ∘ φ) := by sorry
