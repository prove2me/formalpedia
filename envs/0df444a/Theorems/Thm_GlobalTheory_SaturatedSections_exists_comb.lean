-- Prove2me | Theorems.Thm_GlobalTheory_SaturatedSections_exists_comb
-- name    : GlobalTheory.SaturatedSections.exists_comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:10.523819+00:00
-- url     : https://prove2.me/theorems/9c41d756-99bd-4274-9046-80abe3e57f02
-- title:
--   Saturated Sections: exists comb
-- statement:
--   The Saturated Sections construction uses the exists comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueCombOfIndependentSpecialFibre.lean#L10-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueCombOfIndependentSpecialFibre.lean#L10-L34

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
open GlobalTheory GlobalTheory.SaturatedSections

theorem GlobalTheory.SaturatedSections.exists_comb {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    {J : Type} {A : J → Type} [∀ j, CommRing (A j)] (φ : ∀ j, W →+* A j) {ϖ : W}
    (hϖ : Irreducible ϖ) (reg : ∀ j (x : A j), φ j ϖ * x = 0 → x = 0)
    {r : ℕ} (s : Fin r → ∀ j, A j)
    (ind : ∀ (c : Fin r → W) (y : ∀ j, A j), (∀ j, φ j ϖ * y j = ∑ i, φ j (c i) * s i j) →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal W) (n : ℕ) :
    ∀ (t : ∀ j, A j) (c : Fin r → W), (∀ j, φ j (ϖ ^ n) * t j = ∑ i, φ j (c i) * s i j) →
      ∃ d : Fin r → W, (∀ i, c i = ϖ ^ n * d i) ∧ ∀ j, t j = ∑ i, φ j (d i) * s i j := by sorry
