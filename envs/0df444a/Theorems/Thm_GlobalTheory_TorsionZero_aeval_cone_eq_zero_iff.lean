-- Prove2me | Theorems.Thm_GlobalTheory_TorsionZero_aeval_cone_eq_zero_iff
-- name    : GlobalTheory.TorsionZero.aeval_cone_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:09:13.916828+00:00
-- url     : https://prove2.me/theorems/a355fe7f-0642-4d06-9ca5-aa5063291c6c
-- title:
--   Torsion Zero: aeval cone eq zero iff
-- statement:
--   The Torsion Zero construction uses the aeval cone eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L74-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L74-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K σ : Type} [Field K]

theorem GlobalTheory.TorsionZero.aeval_cone_eq_zero_iff {C : Type} [CommRing C] [Algebra K C] (r : σ → C)
    (G : MvPolynomial σ K) :
    aeval (fun j => Polynomial.C (r j) * Polynomial.X) G = 0 ↔
      ∀ n, aeval r (homogeneousComponent n G) = 0 := by sorry
