-- Prove2me | Theorems.Thm_GlobalTheory_exists_form_degree_le_of_isHilbertPoly
-- name    : GlobalTheory.exists_form_degree_le_of_isHilbertPoly
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:17.728937+00:00
-- url     : https://prove2.me/theorems/8b051a7f-c54f-4b15-b4a5-8454483b87da
-- title:
--   Global Theory: exists form degree le of is Hilbert Poly
-- statement:
--   The Global Theory construction uses the exists form degree le of is Hilbert Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L392-L492
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L392-L492

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
open MvPolynomial ProjCut ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι k : Type*} [Field k]

theorem GlobalTheory.exists_form_degree_le_of_isHilbertPoly [Infinite k] [Finite ι]
    {P : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hPh : P.IsHomogeneous (homogeneousSubmodule ι k)) (hne : ∃ i, X i ∉ P)
    {H : Polynomial ℚ} (hH : IsHilbertPoly (quotPiece P) H)
    (y : ι → k) (hy : ∃ f ∈ P, eval y f ≠ 0) :
    ∃ (d : ℕ) (f : MvPolynomial ι k), f ∈ P ∧ f.IsHomogeneous d ∧
      (d : ℚ) ≤ H.natDegree.factorial * H.leadingCoeff ∧ eval y f ≠ 0 := by sorry
