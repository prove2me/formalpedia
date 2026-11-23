-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_IsoBasis_hf_symm
-- name    : GlobalTheory.UTrans.IsoBasis.hf_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:49.107154+00:00
-- url     : https://prove2.me/theorems/e0e2700e-39a3-4652-bf5c-08bf50271227
-- title:
--   Iso Basis: hf symm
-- statement:
--   The Iso Basis construction uses the hf symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsotropicBasisNonorthogonalTwoVectors.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsotropicBasisNonorthogonalTwoVectors.lean#L21-L26

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

theorem GlobalTheory.UTrans.IsoBasis.hf_symm {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E} (hG : IsHerm σ G) (x y : Fin n → E) :
    σ (hf σ G x y) = hf σ G y x := by sorry
