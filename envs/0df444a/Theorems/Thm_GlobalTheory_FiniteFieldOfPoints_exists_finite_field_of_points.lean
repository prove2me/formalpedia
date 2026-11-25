-- Prove2me | Theorems.Thm_GlobalTheory_FiniteFieldOfPoints_exists_finite_field_of_points
-- name    : GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:04:52.234023+00:00
-- url     : https://prove2.me/theorems/296783cb-8d1b-57fd-8f1a-bce52a0f5399
-- title:
--   Finite Field Of Points: exists finite field of points
-- statement:
--   The Finite Field Of Points construction uses the exists finite field of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteFieldOfPoints.lean#L18-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteFieldOfPoints.lean#L18-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteFieldOfPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.FiniteFieldOfPoints

theorem GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points (K : Type) [Field K] (C : Type) [CommRing C] (φ : K →+* C)
    (hφ : RingHom.Finite φ) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)), FiniteDimensional K ↥E ∧
      ∀ (K₂ Ω : Type) [Field K₂] [Field Ω] (e : ↥E →+* K₂) (j : K₂ →+* Ω) (ψ : C →+* Ω),
        RingHom.comp ψ φ = RingHom.comp j (RingHom.comp e (algebraMap K ↥E)) →
        ∃ (ψ₀ : C →+* K₂), RingHom.comp j ψ₀ = ψ := by sorry
