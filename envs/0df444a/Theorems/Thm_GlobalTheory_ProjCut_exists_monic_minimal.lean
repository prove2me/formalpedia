-- Prove2me | Theorems.Thm_GlobalTheory_ProjCut_exists_monic_minimal
-- name    : GlobalTheory.ProjCut.exists_monic_minimal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:56:45.349697+00:00
-- url     : https://prove2.me/theorems/1fcaa68a-14fa-43a4-9924-d092b9ca1430
-- title:
--   Proj Cut: exists monic minimal
-- statement:
--   The Proj Cut construction uses the exists monic minimal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L251-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L251-L271

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module
open GlobalTheory
open GlobalTheory.ProjCut
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι k : Type*} [Field k]

theorem GlobalTheory.ProjCut.exists_monic_minimal {R A : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] (φ : R →+* A) (hinj : Function.Injective φ) (hint : φ.IsIntegral)
    (t : A) : ∃ p : Polynomial R, p.Monic ∧ 0 < p.natDegree ∧ p.eval₂ φ t = 0 ∧
      ∀ a : Fin p.natDegree → R, ∑ j, φ (a j) * t ^ (j : ℕ) = 0 → a = 0 := by sorry
