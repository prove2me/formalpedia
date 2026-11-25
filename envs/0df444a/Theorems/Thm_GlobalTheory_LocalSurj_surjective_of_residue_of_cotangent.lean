-- Prove2me | Theorems.Thm_GlobalTheory_LocalSurj_surjective_of_residue_of_cotangent
-- name    : GlobalTheory.LocalSurj.surjective_of_residue_of_cotangent
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:59.394867+00:00
-- url     : https://prove2.me/theorems/eac802c1-7172-4ee1-9365-12d092f644fd
-- title:
--   Local Surj: surjective of residue of cotangent
-- statement:
--   The Local Surj construction uses the surjective of residue of cotangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SurjectiveOfResidueOfCotangent.lean#L61-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SurjectiveOfResidueOfCotangent.lean#L61-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SurjectiveOfResidueOfCotangent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Matrix TensorProduct
open GlobalTheory GlobalTheory.LocalSurj

theorem GlobalTheory.LocalSurj.surjective_of_residue_of_cotangent (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : R →+* A)
    (hc : IsAdicComplete (maximalIdeal R) R) (hf : IsLocalHom f)
    (hres : ∀ z : A, ∃ r, z - f r ∈ maximalIdeal A)
    (hcot : maximalIdeal A ≤ (maximalIdeal R).map f ⊔ maximalIdeal A ^ 2) :
    Function.Surjective f := by sorry
