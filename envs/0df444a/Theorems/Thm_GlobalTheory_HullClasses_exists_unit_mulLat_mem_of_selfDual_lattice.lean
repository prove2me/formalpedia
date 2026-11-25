-- Prove2me | Theorems.Thm_GlobalTheory_HullClasses_exists_unit_mulLat_mem_of_selfDual_lattice
-- name    : GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:01.861712+00:00
-- url     : https://prove2.me/theorems/d3bc1235-ffd0-4cc5-8edb-a01aa082b04d
-- title:
--   Hull Classes: exists unit mul Lat mem of self Dual lattice
-- statement:
--   The Hull Classes construction uses the exists unit mul Lat mem of self Dual lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSelfDualIntegralHermitianLatticesModUnits.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSelfDualIntegralHermitianLatticesModUnits.lean#L12-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenMulLeftImageLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetCosetsIntegralNormUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSelfDualIntegralHermitianLatticesModUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.HullClasses

theorem GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x →
    ∀ c : K.O, c ≠ 0 → ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧
      ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
        (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) →
        (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
          (algebraMap K.O K.E).range) →
        ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S := by sorry
