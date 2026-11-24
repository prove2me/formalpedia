-- Prove2me | Theorems.Thm_GlobalTheory_LocalSurj_approx_sub_mem
-- name    : GlobalTheory.LocalSurj.approx_sub_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:16:55.538254+00:00
-- url     : https://prove2.me/theorems/ec587f5e-5397-443b-88f8-893f23934a37
-- title:
--   Local Surj: approx sub mem
-- statement:
--   The Local Surj construction uses the approx sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SurjectiveOfResidueOfCotangent.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SurjectiveOfResidueOfCotangent.lean#L49-L59

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

theorem GlobalTheory.LocalSurj.approx_sub_mem {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) {k n : ℕ} (h : k ≤ n) :
    (approx f m hm a n).1 - (approx f m hm a k).1 ∈ m ^ k := by sorry
