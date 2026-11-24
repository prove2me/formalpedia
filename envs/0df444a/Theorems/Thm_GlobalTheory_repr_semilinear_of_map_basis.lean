-- Prove2me | Theorems.Thm_GlobalTheory_repr_semilinear_of_map_basis
-- name    : GlobalTheory.repr_semilinear_of_map_basis
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:16:13.253933+00:00
-- url     : https://prove2.me/theorems/bd921312-cd45-450e-bb6e-c4af405e6e29
-- title:
--   Global Theory: repr semilinear of map basis
-- statement:
--   The Global Theory construction uses the repr semilinear of map basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L537-L541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L537-L541

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {S R Λ M l : Type*} [CommRing S] [CommRing R] [Finite (MaximalSpectrum R)]
  [AddCommGroup Λ] [Module S Λ] [AddCommGroup M] [Module R M] [Fintype l]
  {f : S →+* R} {B : LinearMap.BilinForm S Λ} {B' : LinearMap.BilinForm R M}
omit [Finite (MaximalSpectrum R)]

theorem GlobalTheory.repr_semilinear_of_map_basis {ι : Type*} [Fintype ι] (φ : Λ →ₛₗ[f] M) {b : Basis ι S Λ}
    {c : Basis ι R M} (h : ∀ i, φ (b i) = c i) (x : Λ) (i : ι) :
    c.repr (φ x) i = f (b.repr x i) := by sorry
