-- Prove2me | Theorems.Thm_GlobalTheory_isOpen_of_stableUnderGeneralization_of_locally_open_in_closure
-- name    : GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:58:29.321825+00:00
-- url     : https://prove2.me/theorems/6c8cdf45-0112-4d07-b161-6d7331bd1dfc
-- title:
--   Global Theory: is Open of stable Under Generalization of locally open in closure
-- statement:
--   The Global Theory construction uses the is Open of stable Under Generalization of locally open in closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenOfStableUnderGeneralizationOfLocallyOpen.lean#L6-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenOfStableUnderGeneralizationOfLocallyOpen.lean#L6-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.isOpen_of_stableUnderGeneralization_of_locally_open_in_closure :
    ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (U : Set (PrimeSpectrum B)),
      (∀ p q : PrimeSpectrum B, p ≤ q → q ∈ U → p ∈ U) →
      (∀ p ∈ U, ∃ g, g ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum B, p ≤ q → g ∉ q.asIdeal → q ∈ U) →
      IsOpen U := by sorry
