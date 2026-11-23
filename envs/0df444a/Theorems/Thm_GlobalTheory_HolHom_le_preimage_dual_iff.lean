-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_le_preimage_dual_iff
-- name    : GlobalTheory.HolHom.le_preimage_dual_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:46:22.193438+00:00
-- url     : https://prove2.me/theorems/f045cfac-ba28-473f-b08f-2c0f4bb7154b
-- title:
--   Hol Hom: le preimage dual iff
-- statement:
--   The Hol Hom construction uses the le preimage dual iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L85-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L85-L94

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

theorem GlobalTheory.HolHom.le_preimage_dual_iff {v : Sp (DualNumber ℂ) ⟶ X} {x : Sp ℂ ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) (U : X.Opens) : ⊤ ≤ v ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by sorry
