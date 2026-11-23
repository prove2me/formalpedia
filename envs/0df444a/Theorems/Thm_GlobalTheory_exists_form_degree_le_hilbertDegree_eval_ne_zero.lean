-- Prove2me | Theorems.Thm_GlobalTheory_exists_form_degree_le_hilbertDegree_eval_ne_zero
-- name    : GlobalTheory.exists_form_degree_le_hilbertDegree_eval_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:35.989209+00:00
-- url     : https://prove2.me/theorems/2c2befc3-72d4-4d90-8693-ec03ee97c71c
-- title:
--   Global Theory: exists form degree le hilbert Degree eval ne zero
-- statement:
--   The Global Theory construction uses the exists form degree le hilbert Degree eval ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L494-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L494-L502

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

theorem GlobalTheory.exists_form_degree_le_hilbertDegree_eval_ne_zero [Infinite k] [Finite ι]
    {P : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hPh : P.IsHomogeneous (homogeneousSubmodule ι k)) (hne : ∃ i, X i ∉ P)
    (y : ι → k) (hy : ∃ f ∈ P, eval y f ≠ 0) :
    ∃ d ≤ hilbertDegree P, ∃ f ∈ P, f.IsHomogeneous d ∧ eval y f ≠ 0 := by sorry
