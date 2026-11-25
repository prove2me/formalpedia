-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_selfDualIntegral_hermitianLattices_modUnits
-- name    : GlobalTheory.T.finite_selfDualIntegral_hermitianLattices_modUnits
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:34:49.928812+00:00
-- url     : https://prove2.me/theorems/c5f5f449-5a1b-4a1c-8cb4-b74cfa255d67
-- title:
--   T: finite self Dual Integral hermitian Lattices mod Units
-- statement:
--   The T construction uses the finite self Dual Integral hermitian Lattices mod Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSelfDualIntegralHermitianLatticesModUnitsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSelfDualIntegralHermitianLatticesModUnitsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSelfDualIntegralHermitianLatticesModUnits
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSelfDualIntegralHermitianLatticesModUnitsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_selfDualIntegral_hermitianLattices_modUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → ∀ c : K.O, c ≠ 0 → ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧ ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) → (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) → (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range) → ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S := by sorry
