-- Prove2me | Theorems.Thm_GlobalTheory_ProjCut_isIntegral_of_projection
-- name    : GlobalTheory.ProjCut.isIntegral_of_projection
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:51:56.254807+00:00
-- url     : https://prove2.me/theorems/b5fe7d34-33e0-4ee4-94c1-d4199b9ab95c
-- title:
--   Proj Cut: is Integral of projection
-- statement:
--   The Proj Cut construction uses the is Integral of projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L77-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L77-L140

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

theorem GlobalTheory.ProjCut.isIntegral_of_projection {σ R A : Type*} [Fintype σ] [CommRing R] [Algebra k R]
    [CommRing A] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
    (w : σ → A) (a : σ → R) (c : σ → k) (t : A)
    (h : ∀ j, w j = algebraMap k A (c j) * t + algebraMap R A (a j))
    {g : MvPolynomial σ k} {m : ℕ} (hg : g.IsHomogeneous m) (hw : aeval w g = 0)
    (hc : eval c g ≠ 0)
    (hint : (aeval w : MvPolynomial σ k →ₐ[k] A).toRingHom.IsIntegral) :
    Algebra.IsIntegral R A := by sorry
