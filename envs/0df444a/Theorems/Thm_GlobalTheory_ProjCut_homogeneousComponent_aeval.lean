-- Prove2me | Theorems.Thm_GlobalTheory_ProjCut_homogeneousComponent_aeval
-- name    : GlobalTheory.ProjCut.homogeneousComponent_aeval
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:54.469642+00:00
-- url     : https://prove2.me/theorems/16a00e7a-40da-4e79-bf9f-3fcc7891249e
-- title:
--   Proj Cut: homogeneous Component aeval
-- statement:
--   The Proj Cut construction uses the homogeneous Component aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L142-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L142-L154

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
open ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
variable {ι k : Type*} [Field k]

theorem GlobalTheory.ProjCut.homogeneousComponent_aeval {σ : Type*} (w : σ → MvPolynomial ι k)
    (hw : ∀ j, (w j).IsHomogeneous 1) (n : ℕ) (g : MvPolynomial σ k) :
    homogeneousComponent n (aeval w g) = aeval w (homogeneousComponent n g) := by sorry
