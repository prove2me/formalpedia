-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_holAt_of_isPullback
-- name    : GlobalTheory.HolHom.holAt_of_isPullback
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:18.738808+00:00
-- url     : https://prove2.me/theorems/d06fe850-0e5a-4e74-aaeb-c2e6a6b72fe9
-- title:
--   Hol Hom: hol At of is Pullback
-- statement:
--   The Hol Hom construction uses the hol At of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L161-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L161-L201

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

theorem GlobalTheory.HolHom.holAt_of_isPullback {Y S Z : Scheme.{0}} {f : Y ⟶ S} {g : Z ⟶ X} {iX : X ⟶ S} {iY : Z ⟶ Y}
    (H : IsPullback g iY iX f) {c : V → (Sp ℂ ⟶ Z)} {z : V}
    (h₁ : HolAt (fun t => c t ≫ g) z) (h₂ : HolAt (fun t => c t ≫ iY) z) : HolAt c z := by sorry
