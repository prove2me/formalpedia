-- Prove2me | Theorems.Thm_GlobalTheory_DVRQuotCount_irreducible_dvd
-- name    : GlobalTheory.DVRQuotCount.irreducible_dvd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:35:22.596559+00:00
-- url     : https://prove2.me/theorems/b8c76b34-e846-4c95-9979-7966490c0d2a
-- title:
--   DVRQuot Count: irreducible dvd
-- statement:
--   The DVRQuot Count construction uses the irreducible dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardQuotPowSmulBoundsDvrFgModule.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardQuotPowSmulBoundsDvrFgModule.lean#L41-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotPowSmulBoundsDvrFgModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open GlobalTheory GlobalTheory.DVRQuotCount
open scoped TensorProduct DirectSum

theorem GlobalTheory.DVRQuotCount.irreducible_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p t : O}
    (hp : Irreducible p) (ht : t ≠ 0) (htu : ¬ IsUnit t) : p ∣ t := by sorry
