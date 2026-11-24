-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_forall_algHom_complex
-- name    : GlobalTheory.eq_zero_of_forall_algHom_complex
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:03.629811+00:00
-- url     : https://prove2.me/theorems/4b257bba-9878-40f5-be28-6dfa2d0e12b0
-- title:
--   Global Theory: eq zero of forall alg Hom complex
-- statement:
--   The Global Theory construction uses the eq zero of forall alg Hom complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/EqZeroOfForallAlgHomComplex.lean#L11-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/EqZeroOfForallAlgHomComplex.lean#L11-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.eq_zero_of_forall_algHom_complex {A : Type*} [CommRing A] [Algebra ℂ A] [_root_.IsReduced A]
    [Algebra.FiniteType ℂ A] (a : A) (h : ∀ e : A →ₐ[ℂ] ℂ, e a = 0) : a = 0 := by sorry
