-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_isHolTo_of_holAt
-- name    : GlobalTheory.HolHom.isHolTo_of_holAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:44:59.753683+00:00
-- url     : https://prove2.me/theorems/03876904-7935-4429-8b8d-c06bb75050a1
-- title:
--   Hol Hom: is Hol To of hol At
-- statement:
--   The Hol Hom construction uses the is Hol To of hol At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L114-L118

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

theorem GlobalTheory.HolHom.isHolTo_of_holAt {B : Set V} {c : V → (Sp ℂ ⟶ X)} (hB : IsOpen B) (h : ∀ z ∈ B, HolAt c z) :
    IsHolTo B c := by sorry
