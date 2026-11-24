-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_PlaneRefl_quasiRefl_eq_mul_of_plane
-- name    : GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:21:07.553108+00:00
-- url     : https://prove2.me/theorems/4507805d-d9ab-45be-a635-30127ef93535
-- title:
--   Plane Refl: quasi Refl eq mul of plane
-- statement:
--   The Plane Refl construction uses the quasi Refl eq mul of plane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/QuasiReflectionEqMulTransvectionsOfHyperbolicPla.lean#L169-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/QuasiReflectionEqMulTransvectionsOfHyperbolicPla.lean#L169-L244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpecialUnitaryHyperbolicPlaneMemTransvections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqMulTransvectionsOfHyperbolicPla
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.PlaneRefl
variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)

theorem GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane : ∀ (E : Type) [Field E] [CharZero E]
    (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.UTrans.IsHerm σ G →
    ∀ (x z : Fin n → E) (a u : E), _root_.GlobalTheory.UTrans.hf σ G z z = 0 →
    _root_.GlobalTheory.UTrans.hf σ G x z ≠ 0 → _root_.GlobalTheory.UTrans.hf σ G x x ≠ 0 →
    _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z) ≠ 0 → u * σ u = 1 →
    ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen σ G,
      _root_.GlobalTheory.UTrans.tv σ G x ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G x x) =
        m * _root_.GlobalTheory.UTrans.tv σ G (x + a • z)
          ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z)) := by sorry
