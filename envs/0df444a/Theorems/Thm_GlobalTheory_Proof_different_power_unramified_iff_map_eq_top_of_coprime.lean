-- Prove2me | Theorems.Thm_GlobalTheory_Proof_different_power_unramified_iff_map_eq_top_of_coprime
-- name    : GlobalTheory.Proof.different_power_unramified_iff.map_eq_top_of_coprime
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:11:58.215162+00:00
-- url     : https://prove2.me/theorems/b06c4081-d447-46ee-b41e-4254f6ba1e86
-- title:
--   different power unramified iff: map eq top of coprime
-- statement:
--   The different power unramified iff construction uses the map eq top of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DifferentPowerUnramifiedIff.lean#L41-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DifferentPowerUnramifiedIff.lean#L41-L57

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

theorem GlobalTheory.Proof.different_power_unramified_iff.map_eq_top_of_coprime {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S]
    (f : R →+* S) (P : Ideal R) (hP : P.IsMaximal)
    (h : ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map f = ⊤) (Q : Ideal R) (hQ : Q ≠ ⊥)
    (hPQ : P ⊔ Q = ⊤) : Q.map f = ⊤ := by sorry
