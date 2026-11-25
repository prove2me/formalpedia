-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_isUnit_matrix_of_pow_smul_span_invert
-- name    : GlobalTheory.T.exists_isUnit_matrix_of_pow_smul_span_invert
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:14.571825+00:00
-- url     : https://prove2.me/theorems/d63b0865-dd98-4aa2-80bf-f2aa7b955ffc
-- title:
--   T: exists is Unit matrix of pow smul span invert
-- statement:
--   The T construction uses the exists is Unit matrix of pow smul span invert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsUnitMatrixOfPowSmulSpanInvertStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsUnitMatrixOfPowSmulSpanInvertStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsUnitMatrixOfPowSmulSpanInvert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsUnitMatrixOfPowSmulSpanInvertStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_isUnit_matrix_of_pow_smul_span_invert : ∀ (S EE W RW Y : Type) [CommRing S] [CommRing EE] [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW) (c : W →+* RW) (ψ : S →+* W) (Q : S), Function.Injective ι → (∀ s, ι (a s) = c (ψ s)) → IsUnit (a Q) → ∀ (q : ℕ) (x z : Fin q → Y), (∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) → (∀ j, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • z j = ∑ i, c (ψ (s i)) • x i) → (∀ i, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • x i = ∑ j, c (ψ (s j)) • z j) → ∃ A : Matrix (Fin q) (Fin q) EE, IsUnit A ∧ ∀ j, z j = ∑ i, ι (A i j) • x i := by sorry
