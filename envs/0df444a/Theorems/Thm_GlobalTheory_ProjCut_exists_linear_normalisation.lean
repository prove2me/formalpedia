-- Prove2me | Theorems.Thm_GlobalTheory_ProjCut_exists_linear_normalisation
-- name    : GlobalTheory.ProjCut.exists_linear_normalisation
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:19.555297+00:00
-- url     : https://prove2.me/theorems/371b701a-96d5-4179-b067-dcad15d48a4e
-- title:
--   Proj Cut: exists linear normalisation
-- statement:
--   The Proj Cut construction uses the exists linear normalisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L156-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormDegreeLeHilbertDegreeEvalNeZero.lean#L156-L209

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

theorem GlobalTheory.ProjCut.exists_linear_normalisation [Infinite k] {P : Ideal (MvPolynomial ι k)} (hP : P ≠ ⊤)
    (hPh : P.IsHomogeneous (homogeneousSubmodule ι k)) (y : ι → k) (r : ℕ)
    (w : Fin r → MvPolynomial ι k) (hw : ∀ j, (w j).IsHomogeneous 1)
    (hy : ∀ j, eval y (w j) = 0)
    (hint : (aeval fun j => Ideal.Quotient.mk P (w j) :
      MvPolynomial (Fin r) k →ₐ[k] _).toRingHom.IsIntegral) :
    ∃ (s : ℕ) (z : Fin s → MvPolynomial ι k), (∀ j, (z j).IsHomogeneous 1) ∧
      (∀ j, eval y (z j) = 0) ∧
      (aeval fun j => Ideal.Quotient.mk P (z j) :
        MvPolynomial (Fin s) k →ₐ[k] _).toRingHom.IsIntegral ∧
      Function.Injective (aeval fun j => Ideal.Quotient.mk P (z j) :
        MvPolynomial (Fin s) k →ₐ[k] _) := by sorry
