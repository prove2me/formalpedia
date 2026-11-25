-- Prove2me | Theorems.Thm_GlobalTheory_ProjCut_ringKrullDim_eq_natDegree_idealHilbertPoly
-- name    : GlobalTheory.ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:29.948174+00:00
-- url     : https://prove2.me/theorems/88779c89-5588-4bb3-a6c6-de11c2a967e1
-- title:
--   Proj Cut: ring Krull Dim eq nat Degree ideal Hilbert Poly
-- statement:
--   The Proj Cut construction uses the ring Krull Dim eq nat Degree ideal Hilbert Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L336-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L336-L380

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

theorem GlobalTheory.ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly [Infinite k] [Finite ι]
    {P : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hPh : P.IsHomogeneous (homogeneousSubmodule ι k)) (hne : ∃ i, X i ∉ P) :
    ringKrullDim (MvPolynomial ι k ⧸ P) = ((idealHilbertPoly P).natDegree + 1 : ℕ) := by sorry
