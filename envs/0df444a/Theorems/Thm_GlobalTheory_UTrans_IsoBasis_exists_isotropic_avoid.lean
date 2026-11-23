-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_IsoBasis_exists_isotropic_avoid
-- name    : GlobalTheory.UTrans.IsoBasis.exists_isotropic_avoid
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:31:26.675916+00:00
-- url     : https://prove2.me/theorems/8ddf55d2-6209-4e88-bc21-73f0c22efd52
-- title:
--   Iso Basis: exists isotropic avoid
-- statement:
--   The Iso Basis construction uses the exists isotropic avoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsotropicBasisNonorthogonalTwoVectors.lean#L50-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsotropicBasisNonorthogonalTwoVectors.lean#L50-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectors
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
noncomputable section
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.IsoBasis
variable {E : Type} [Field E] {n : ℕ}

theorem GlobalTheory.UTrans.IsoBasis.exists_isotropic_avoid [CharZero E] {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
    (hG : IsHerm σ G) (hz : ∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0)
    {ι : Type} [Finite ι] (f : ι → (Fin n → E) →ₗ[E] E) (hf0 : ∀ i, ∃ x, f i x ≠ 0) :
    ∃ z, hf σ G z z = 0 ∧ ∀ i, f i z ≠ 0 := by sorry
