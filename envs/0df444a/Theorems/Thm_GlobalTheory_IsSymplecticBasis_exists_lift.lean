-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_exists_lift
-- name    : GlobalTheory.IsSymplecticBasis.exists_lift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:22:01.861804+00:00
-- url     : https://prove2.me/theorems/2794acf2-2689-4b18-aaab-5b11b1e10e2a
-- title:
--   Is Symplectic Basis: exists lift
-- statement:
--   The Is Symplectic Basis construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L543-L556
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L543-L556

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

theorem GlobalTheory.IsSymplecticBasis.exists_lift (hf : Surjective f) (hB : B.IsAlt) (hB' : B'.IsAlt)
    (φ : Λ →ₛₗ[f] M) {b : Basis (l ⊕ l) S Λ} {b' : Basis (l ⊕ l) R M}
    (hb : IsSymplecticBasis B b) (hb' : IsSymplecticBasis B' b') (h : ∀ i, φ (b i) = b' i)
    {c' : Basis (l ⊕ l) R M} (hc' : IsSymplecticBasis B' c') :
    ∃ c : Basis (l ⊕ l) S Λ, IsSymplecticBasis B c ∧ ∀ i, φ (c i) = c' i := by sorry
