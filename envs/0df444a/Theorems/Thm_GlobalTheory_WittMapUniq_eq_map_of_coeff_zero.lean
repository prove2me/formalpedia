-- Prove2me | Theorems.Thm_GlobalTheory_WittMapUniq_eq_map_of_coeff_zero
-- name    : GlobalTheory.WittMapUniq.eq_map_of_coeff_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:15.636881+00:00
-- url     : https://prove2.me/theorems/316c4e9b-cbce-4461-84a0-6a9868d17df4
-- title:
--   Witt Map Uniq: eq map of coeff zero
-- statement:
--   The Witt Map Uniq construction uses the eq map of coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorRingHomEqMapOfCoeffZero.lean#L20-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorRingHomEqMapOfCoeffZero.lean#L20-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorRingHomEqMapOfCoeffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.WittMapUniq
open WittVector

theorem GlobalTheory.WittMapUniq.eq_map_of_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] [CommRing O] [CharP O l] [PerfectRing O l]
    (F : WittVector l R →+* WittVector l O) (ψ : R →+* O),
    (∀ a, (F a).coeff 0 = ψ (a.coeff 0)) → F = WittVector.map ψ := by sorry
