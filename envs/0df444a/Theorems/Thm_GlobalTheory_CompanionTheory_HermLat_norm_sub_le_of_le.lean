-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_norm_sub_le_of_le
-- name    : GlobalTheory.CompanionTheory.HermLat.norm_sub_le_of_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:48:02.252804+00:00
-- url     : https://prove2.me/theorems/d17cc782-b68e-4671-9312-88b13ccf5b5c
-- title:
--   Herm Lat: norm sub le of le
-- statement:
--   The Herm Lat construction uses the norm sub le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatement.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatement.lean#L80-L82

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V]
  [Module L V] {s : L →+* L} {δ : L} {h : V → V → L}

theorem GlobalTheory.CompanionTheory.HermLat.norm_sub_le_of_le {a b : L} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by sorry
