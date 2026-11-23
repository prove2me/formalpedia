-- Prove2me | Theorems.Thm_GlobalTheory_ProjCut_mk_mul_mem_quotPiece
-- name    : GlobalTheory.ProjCut.mk_mul_mem_quotPiece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:10.180324+00:00
-- url     : https://prove2.me/theorems/7e69b4aa-ed43-49cf-b5fd-b7ff8632fe2d
-- title:
--   Proj Cut: mk mul mem quot Piece
-- statement:
--   The Proj Cut construction uses the mk mul mem quot Piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L54-L62

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

theorem GlobalTheory.ProjCut.mk_mul_mem_quotPiece (I : Ideal (MvPolynomial ι k)) {z : MvPolynomial ι k}
    (hz : z.IsHomogeneous 1) (n : ℤ) {m : MvPolynomial ι k ⧸ I} (hm : m ∈ quotPiece I n) :
    Ideal.Quotient.mk I z * m ∈ quotPiece I (n + 1) := by sorry
