-- Prove2me | Theorems.Thm_GlobalTheory_ProjCut_degree_lt_of_isIntegral
-- name    : GlobalTheory.ProjCut.degree_lt_of_isIntegral
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:57.159316+00:00
-- url     : https://prove2.me/theorems/38b05a3a-50ce-4bd6-9dc2-6fcbd29f7c59
-- title:
--   Proj Cut: degree lt of is Integral
-- statement:
--   The Proj Cut construction uses the degree lt of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L231-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L231-L249

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

theorem GlobalTheory.ProjCut.degree_lt_of_isIntegral {A : Type*} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (ℳ : ℤ → Submodule k A) [DirectSum.Decomposition ℳ] {H : Polynomial ℚ}
    (hH : IsHilbertPoly ℳ H) {s : ℕ} (z : Fin s → A)
    (hz : ∀ j n, ∀ m ∈ ℳ n, z j * m ∈ ℳ (n + 1))
    (hint : (aeval z : MvPolynomial (Fin s) k →ₐ[k] A).toRingHom.IsIntegral) :
    H.degree < (s : ℕ) := by sorry
