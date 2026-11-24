-- Prove2me | Theorems.Thm_GlobalTheory_isHomogeneous_map_of_surjective
-- name    : GlobalTheory.isHomogeneous_map_of_surjective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:56:58.020956+00:00
-- url     : https://prove2.me/theorems/1bf18615-4659-466b-8046-2398d0ec09e3
-- title:
--   Global Theory: is Homogeneous map of surjective
-- statement:
--   The Global Theory construction uses the is Homogeneous map of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L28-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ ι R : Type*} [CommRing R]

theorem GlobalTheory.isHomogeneous_map_of_surjective {R' : Type*} [CommRing R'] {φ : R →+* R'}
    (hφ : Function.Surjective φ) {I : Ideal (MvPolynomial σ R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) :
    (I.map (map φ)).IsHomogeneous (homogeneousSubmodule σ R') := by sorry
