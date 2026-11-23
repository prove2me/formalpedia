-- Prove2me | Theorems.Thm_GlobalTheory_map_homogeneousComponent_eq
-- name    : GlobalTheory.map_homogeneousComponent_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:35.215558+00:00
-- url     : https://prove2.me/theorems/64bedf43-797e-45fe-9be5-efe7175bf4ff
-- title:
--   Global Theory: map homogeneous Component eq
-- statement:
--   The Global Theory construction uses the map homogeneous Component eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L14-L19

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

theorem GlobalTheory.map_homogeneousComponent_eq {R' : Type*} [CommRing R'] (φ : R →+* R') (n : ℕ)
    (p : MvPolynomial σ R) :
    map φ (homogeneousComponent n p) = homogeneousComponent n (map φ p) := by sorry
