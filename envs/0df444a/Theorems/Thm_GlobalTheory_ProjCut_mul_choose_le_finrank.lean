-- Prove2me | Theorems.Thm_GlobalTheory_ProjCut_mul_choose_le_finrank
-- name    : GlobalTheory.ProjCut.mul_choose_le_finrank
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:15.941558+00:00
-- url     : https://prove2.me/theorems/78f2ec01-7456-4a92-871d-3f0543f40ad2
-- title:
--   Proj Cut: mul choose le finrank
-- statement:
--   The Proj Cut construction uses the mul choose le finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L273-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L273-L307

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

theorem GlobalTheory.ProjCut.mul_choose_le_finrank [Finite ι] (I : Ideal (MvPolynomial ι k)) {e d : ℕ}
    (z : Fin (e + 1) → MvPolynomial ι k) (hz : ∀ j, (z j).IsHomogeneous 1)
    {l : MvPolynomial ι k} (hl : l.IsHomogeneous 1)
    (hind : ∀ a : Fin d → MvPolynomial (Fin (e + 1)) k,
      ∑ j, aeval z (a j) * l ^ (j : ℕ) ∈ I → a = 0) (m : ℕ) :
    d * (m + e).choose e ≤ finrank k (quotPiece I ((m + d : ℕ) : ℤ)) := by sorry
