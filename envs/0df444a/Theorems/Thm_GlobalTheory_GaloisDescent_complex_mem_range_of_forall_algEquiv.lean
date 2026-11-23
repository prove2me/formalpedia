-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_complex_mem_range_of_forall_algEquiv
-- name    : GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:45.684704+00:00
-- url     : https://prove2.me/theorems/0750c539-2e51-4a87-b5ff-b6d9b3320b07
-- title:
--   Galois Descent: complex mem range of forall alg Equiv
-- statement:
--   The Galois Descent construction uses the complex mem range of forall alg Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsRingEquivOfIsTranscendenceBasis.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsRingEquivOfIsTranscendenceBasis.lean#L107-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Cardinal
open GlobalTheory GlobalTheory.GaloisDescent
open MvPolynomial Cardinal

theorem GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv {K : Type*} [Field K] [Algebra K ℂ] (x : ℂ)
    (hx : ∀ σ : ℂ ≃ₐ[K] ℂ, σ x = x) : x ∈ Set.range (algebraMap K ℂ) := by sorry
