-- Prove2me | Theorems.Thm_GlobalTheory_OnePrime_nontrivial_Ow
-- name    : GlobalTheory.OnePrime.nontrivial_Ow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:31:26.685809+00:00
-- url     : https://prove2.me/theorems/bff4689c-f008-4c94-ae69-c728a83d8b2b
-- title:
--   One Prime: nontrivial Ow
-- statement:
--   The One Prime construction uses the nontrivial Ow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueMaximalAbovePlace.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueMaximalAbovePlace.lean#L15-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueMaximalAbovePlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.OnePrime
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

theorem GlobalTheory.OnePrime.nontrivial_Ow (w : Place p R) : Nontrivial w.Ow := by sorry
