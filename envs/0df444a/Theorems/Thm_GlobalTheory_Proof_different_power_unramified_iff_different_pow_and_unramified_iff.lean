-- Prove2me | Theorems.Thm_GlobalTheory_Proof_different_power_unramified_iff_different_pow_and_unramified_iff
-- name    : GlobalTheory.Proof.different_power_unramified_iff.different_pow_and_unramified_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:51.019596+00:00
-- url     : https://prove2.me/theorems/647111da-1c7b-49a9-9cc6-9826ce5f2eea
-- title:
--   different power unramified iff: different pow and unramified iff
-- statement:
--   The different power unramified iff construction uses the different pow and unramified iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DifferentPowerUnramifiedIff.lean#L96-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DifferentPowerUnramifiedIff.lean#L96-L231

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
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem GlobalTheory.Proof.different_power_unramified_iff.different_pow_and_unramified_iff (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R] (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p R)
    (P : Ideal R) (hP : P.IsMaximal) (hpP : (p : R) ∈ P) (hm : (P.map w.toOw).IsMaximal)
    (hQ : ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤) :
    (∃ a b : ℕ, 0 < b ∧ (differentIdeal ℤ R).map w.toOw ^ b = Ideal.span {(p : w.Ow) ^ a}) ∧
      (w.IsUnramified ↔ (differentIdeal ℤ R).map w.toOw = ⊤) := by sorry
