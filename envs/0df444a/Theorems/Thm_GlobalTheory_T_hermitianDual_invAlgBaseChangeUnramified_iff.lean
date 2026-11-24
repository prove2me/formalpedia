-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitianDual_invAlgBaseChangeUnramified_iff
-- name    : GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:46:08.362839+00:00
-- url     : https://prove2.me/theorems/c9d44f7a-f546-4bd0-919e-f0e526803e9b
-- title:
--   T: hermitian Dual inv Alg Base Change Unramified iff
-- statement:
--   The T construction uses the hermitian Dual inv Alg Base Change Unramified iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianDualInvAlgBaseChangeUnramifiedIffStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianDualInvAlgBaseChangeUnramifiedIffStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianDualInvAlgBaseChangeUnramifiedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianDualInvAlgBaseChangeUnramifiedIffStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (x y : B.A), (∀ z ∈ L, (overExt φ B ψ hψ hσ).herm x y z ∈ (algebraMap K'.O K'.E).range) ↔ (∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) := by sorry
