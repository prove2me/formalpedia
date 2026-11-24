-- Prove2me | Theorems.Thm_GlobalTheory_EvenCubicNorm_prodPow_add
-- name    : GlobalTheory.EvenCubicNorm.prodPow_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:05:05.782632+00:00
-- url     : https://prove2.me/theorems/45b6e596-3962-478e-992e-8e9531fe913d
-- title:
--   Even Cubic Norm: prod Pow add
-- statement:
--   The Even Cubic Norm construction uses the prod Pow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEvenCubicUnitMultipleFractionRing.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEvenCubicUnitMultipleFractionRing.lean#L62-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEvenCubicUnitMultipleFractionRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.EvenCubicNorm
open Finset
variable {M : Type*} [CommGroup M] {ι : Type*} [Fintype ι]

theorem GlobalTheory.EvenCubicNorm.prodPow_add (z : ι → ι → M) (e e' : ι → ι → ℤ) :
    prodPow z e * prodPow z e' = prodPow z (fun i j => e i j + e' i j) := by sorry
