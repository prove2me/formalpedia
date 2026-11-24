-- Prove2me | Theorems.Thm_GlobalTheory_FockDetDer_hasDerivAt_det_one_sub_sq
-- name    : GlobalTheory.FockDetDer.hasDerivAt_det_one_sub_sq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:15.667797+00:00
-- url     : https://prove2.me/theorems/3a2f4e8a-51ac-4398-9256-cee3fb5e7ddc
-- title:
--   Fock Det Der: has Deriv At det one sub sq
-- statement:
--   The Fock Det Der construction uses the has Deriv At det one sub sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SymmetricBlockTraceInverseEqTwoMul.lean#L59-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SymmetricBlockTraceInverseEqTwoMul.lean#L59-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SymmetricBlockTraceInverseEqTwoMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.FockDetDer

theorem GlobalTheory.FockDetDer.hasDerivAt_det_one_sub_sq : ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ) (t : ℝ), IsUnit (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det → let S : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 Aᴴᵀ Aᴴ 0; let T : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 B Bᵀ 0; IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det ∧ HasDerivAt (fun s : ℝ => (1 - ((s : ℂ) ^ 2) • (Aᴴ * B)).det) (-((t : ℂ) * (T * S * (1 - ((t : ℂ) ^ 2) • (T * S))⁻¹).trace) * (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det) t := by sorry
