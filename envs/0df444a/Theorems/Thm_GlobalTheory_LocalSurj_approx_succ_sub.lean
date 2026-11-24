-- Prove2me | Theorems.Thm_GlobalTheory_LocalSurj_approx_succ_sub
-- name    : GlobalTheory.LocalSurj.approx_succ_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:18:52.17563+00:00
-- url     : https://prove2.me/theorems/d2b5cbab-bab8-4142-a2bf-dd4dcb547dee
-- title:
--   Local Surj: approx succ sub
-- statement:
--   The Local Surj construction uses the approx succ sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SurjectiveOfResidueOfCotangent.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SurjectiveOfResidueOfCotangent.lean#L43-L47

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

theorem GlobalTheory.LocalSurj.approx_succ_sub {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) (n : ℕ) :
    (approx f m hm a (n + 1)).1 - (approx f m hm a n).1 ∈ m ^ n := by sorry
