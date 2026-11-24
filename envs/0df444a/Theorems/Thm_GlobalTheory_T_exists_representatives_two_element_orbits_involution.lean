-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_representatives_two_element_orbits_involution
-- name    : GlobalTheory.T.exists_representatives_two_element_orbits_involution
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:38:35.873811+00:00
-- url     : https://prove2.me/theorems/bf58f2a3-efe1-4f5d-b489-58f57012fe17
-- title:
--   T: exists representatives two element orbits involution
-- statement:
--   The T construction uses the exists representatives two element orbits involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRepresentativesTwoElementOrbitsInvolutionStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRepresentativesTwoElementOrbitsInvolutionStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRepresentativesTwoElementOrbitsInvolution
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRepresentativesTwoElementOrbitsInvolutionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_representatives_two_element_orbits_involution : ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧ ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by sorry
