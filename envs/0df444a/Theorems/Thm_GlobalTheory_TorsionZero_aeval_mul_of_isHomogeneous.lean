-- Prove2me | Theorems.Thm_GlobalTheory_TorsionZero_aeval_mul_of_isHomogeneous
-- name    : GlobalTheory.TorsionZero.aeval_mul_of_isHomogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:45:05.578103+00:00
-- url     : https://prove2.me/theorems/b546778b-824d-4088-8c97-ec90aee8b799
-- title:
--   Torsion Zero: aeval mul of is Homogeneous
-- statement:
--   The Torsion Zero construction uses the aeval mul of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L12-L24

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

theorem GlobalTheory.TorsionZero.aeval_mul_of_isHomogeneous {S : Type} [CommRing S] [Algebra K S] (a : σ → S) (w : S)
    {G : MvPolynomial σ K} {n : ℕ} (hG : G.IsHomogeneous n) :
    aeval (fun j => a j * w) G = aeval a G * w ^ n := by sorry
