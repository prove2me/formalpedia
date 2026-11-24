-- Prove2me | Theorems.Thm_GlobalTheory_involution_pair_representatives
-- name    : GlobalTheory.involution_pair_representatives
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:06.815813+00:00
-- url     : https://prove2.me/theorems/7331ae7d-ef30-4d0f-8208-57c5ae202f99
-- title:
--   Global Theory: involution pair representatives
-- statement:
--   The Global Theory construction uses the involution pair representatives property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRepresentativesTwoElementOrbitsInvolution.lean#L5-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRepresentativesTwoElementOrbitsInvolution.lean#L5-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRepresentativesTwoElementOrbitsInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.involution_pair_representatives :
    ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι),
      (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧
        ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by sorry
