-- Prove2me | Theorems.Thm_GlobalTheory_T_wittVector_ringHom_eq_map_of_coeff_zero
-- name    : GlobalTheory.T.wittVector_ringHom_eq_map_of_coeff_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:01:20.20955+00:00
-- url     : https://prove2.me/theorems/7132f56a-4178-4dad-ac16-b4067ca289e7
-- title:
--   T: witt Vector ring Hom eq map of coeff zero
-- statement:
--   The T construction uses the witt Vector ring Hom eq map of coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorRingHomEqMapOfCoeffZeroStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorRingHomEqMapOfCoeffZeroStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorRingHomEqMapOfCoeffZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorRingHomEqMapOfCoeffZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.wittVector_ringHom_eq_map_of_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] [PerfectRing O l] (F : WittVector l R →+* WittVector l O) (ψ : R →+* O), (∀ a, (F a).coeff 0 = ψ (a.coeff 0)) → F = WittVector.map ψ := by sorry
