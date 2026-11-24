-- Prove2me | Theorems.Thm_GlobalTheory_sum_coeff_idealHilbertPoly_minimalPrimes_le
-- name    : GlobalTheory.sum_coeff_idealHilbertPoly_minimalPrimes_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:10.732951+00:00
-- url     : https://prove2.me/theorems/c2c8874f-2371-42f8-b9cd-233ded8620a0
-- title:
--   Global Theory: sum coeff ideal Hilbert Poly minimal Primes le
-- statement:
--   The Global Theory construction uses the sum coeff ideal Hilbert Poly minimal Primes le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L339-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L339-L382

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
variable [Finite ι]

theorem GlobalTheory.sum_coeff_idealHilbertPoly_minimalPrimes_le {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {e : ℕ}
    (he : (idealHilbertPoly I).degree ≤ e) :
    ∑ Q ∈ I.finite_minimalPrimes_of_isNoetherianRing.toFinset, (idealHilbertPoly Q).coeff e ≤
      (idealHilbertPoly I).coeff e := by sorry
