-- Prove2me | Theorems.Thm_GlobalTheory_ProjCut_le_factorial_mul_leadingCoeff
-- name    : GlobalTheory.ProjCut.le_factorial_mul_leadingCoeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:05.824831+00:00
-- url     : https://prove2.me/theorems/ad5f8f83-6107-44a7-95e5-32c3120d3074
-- title:
--   Proj Cut: le factorial mul leading Coeff
-- statement:
--   The Proj Cut construction uses the le factorial mul leading Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L309-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L309-L334

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

theorem GlobalTheory.ProjCut.le_factorial_mul_leadingCoeff [Finite ι] {I : Ideal (MvPolynomial ι k)} {e d : ℕ}
    {H : Polynomial ℚ} (hH : IsHilbertPoly (quotPiece I) H) (hdeg : H.degree ≤ (e : ℕ))
    (hd : 0 < d) (h : ∀ m, d * (m + e).choose e ≤ finrank k (quotPiece I ((m + d : ℕ) : ℤ))) :
    H.natDegree = e ∧ (d : ℚ) ≤ H.natDegree.factorial * H.leadingCoeff := by sorry
