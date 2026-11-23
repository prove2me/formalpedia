-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_point_ext
-- name    : GlobalTheory.HolHom.point_ext
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:09.640264+00:00
-- url     : https://prove2.me/theorems/fa3a4558-c321-419d-8c80-c791103f1a6f
-- title:
--   Hol Hom: point ext
-- statement:
--   The Hol Hom construction uses the point ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L54-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {A : Type} [CommRing A] {X : Scheme.{0}}

theorem GlobalTheory.HolHom.point_ext {x x' : Sp A ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (hx : ⊤ ≤ x ⁻¹ᵁ U) (hx' : ⊤ ≤ x' ⁻¹ᵁ U)
    (h : ∀ f, valR x U f = valR x' U f) : x = x' := by sorry
