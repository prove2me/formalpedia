-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_comb_of_independent_special_fibre
-- name    : GlobalTheory.existsUnique_comb_of_independent_special_fibre
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:29:38.202183+00:00
-- url     : https://prove2.me/theorems/169a284c-0028-4190-bc21-f9f44581cea0
-- title:
--   Global Theory: exists Unique comb of independent special fibre
-- statement:
--   The Global Theory construction uses the exists Unique comb of independent special fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueCombOfIndependentSpecialFibre.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueCombOfIndependentSpecialFibre.lean#L109-L117

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueCombOfIndependentSpecialFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SaturatedSections

theorem GlobalTheory.existsUnique_comb_of_independent_special_fibre : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (H : Scheme.{0}) (p : H ⟶ Sp W) [Flat p] (M : LB H), M.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec M), (∀ c : Fin r → W, (∀ (j : M.ι) (x : H), x ∈ M.U j → p x = IsLocalRing.closedPoint W → x ∉ H.basicOpen (∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j)) → ∀ i, c i ∈ IsLocalRing.maximalIdeal W) → ∀ t : LB.Sec M, (∃ (a : W) (c : Fin r → W), a ≠ 0 ∧ ∀ j, Out.resTop _ (Out.scal p a) * t.f j = ∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j) → ∃! c : Fin r → W, ∀ j, t.f j = ∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j := by sorry
