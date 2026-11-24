-- Prove2me | Theorems.Thm_GlobalTheory_finrank_totalDegree_image_growth
-- name    : GlobalTheory.finrank_totalDegree_image_growth
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:51:02.41475+00:00
-- url     : https://prove2.me/theorems/c963c3d0-428e-42d3-a0d6-83ae84d0bcaa
-- title:
--   Global Theory: finrank total Degree image growth
-- statement:
--   The Global Theory construction uses the finrank total Degree image growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankTotalDegreeImageGrowth.lean#L191-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankTotalDegreeImageGrowth.lean#L191-L228

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.finrank_totalDegree_image_growth : ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] (m g : ℕ) (r : Fin m → B), Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B) → Algebra.trdeg K B = g → ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ g ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ∧ Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ≤ C * t ^ g := by sorry
