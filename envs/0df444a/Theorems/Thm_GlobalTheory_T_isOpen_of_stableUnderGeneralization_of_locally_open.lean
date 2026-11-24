-- Prove2me | Theorems.Thm_GlobalTheory_T_isOpen_of_stableUnderGeneralization_of_locally_open
-- name    : GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_locally_open
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:49:22.798269+00:00
-- url     : https://prove2.me/theorems/0f2595b1-682a-4ec5-8956-8f77eebfade8
-- title:
--   T: is Open of stable Under Generalization of locally open
-- statement:
--   The T construction uses the is Open of stable Under Generalization of locally open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenOfStableUnderGeneralizationOfLocallyOpenStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenOfStableUnderGeneralizationOfLocallyOpenStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyOpen
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyOpenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_locally_open : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (U : Set (PrimeSpectrum B)), (∀ p q : PrimeSpectrum B, p ≤ q → q ∈ U → p ∈ U) → (∀ p ∈ U, ∃ g, g ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum B, p ≤ q → g ∉ q.asIdeal → q ∈ U) → IsOpen U := by sorry
