-- Prove2me | Theorems.Thm_GlobalTheory_Proof_different_power_unramified_iff_ow_p_torsionFree
-- name    : GlobalTheory.Proof.different_power_unramified_iff.ow_p_torsionFree
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:06.909437+00:00
-- url     : https://prove2.me/theorems/eb1af4e6-352a-4ceb-8b71-27e6e83eacea
-- title:
--   different power unramified iff: ow p torsion Free
-- statement:
--   The different power unramified iff construction uses the ow p torsion Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DifferentPowerUnramifiedIff.lean#L24-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DifferentPowerUnramifiedIff.lean#L24-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DifferentPowerUnramifiedIff
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
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.different_power_unramified_iff
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

theorem GlobalTheory.Proof.different_power_unramified_iff.ow_p_torsionFree (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Module.Finite ℤ R] (w : Place p R) (x : w.Ow) (hx : (p : w.Ow) * x = 0) : x = 0 := by sorry
