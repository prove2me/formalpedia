-- Prove2me | Theorems.Thm_GlobalTheory_HullClasses_finite_mod_T_of
-- name    : GlobalTheory.HullClasses.finite_mod_T_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:12:28.882813+00:00
-- url     : https://prove2.me/theorems/bc7778c8-e038-4f0a-8e68-456b7c6c08d0
-- title:
--   Hull Classes: finite mod T of
-- statement:
--   The Hull Classes construction uses the finite mod T of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L107-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L107-L210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.HullClasses

theorem GlobalTheory.HullClasses.finite_mod_T_of (K : UQ) (B : InvAlg K)
    (hPr : ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
      ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)))
    (hNu : ∃ F : Finset B.Aˣ, ∀ u : B.Aˣ, (∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u) →
      ∃ f ∈ F, ∃ t ∈ B.T, u * f⁻¹ * t⁻¹ ∈ intUnits K.O B.A)
    (hBe : ∀ (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 →
      {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite)
    (x : B.A) (c : K.O) (hc0 : c ≠ 0) :
    ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧
      ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
        (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) →
        (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
          (algebraMap K.O K.E).range) →
        ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S := by sorry
