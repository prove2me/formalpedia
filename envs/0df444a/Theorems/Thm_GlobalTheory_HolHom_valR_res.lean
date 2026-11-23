-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_valR_res
-- name    : GlobalTheory.HolHom.valR_res
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:03.442373+00:00
-- url     : https://prove2.me/theorems/5e7465e2-4b03-48e6-b359-c1aa2a9bd0c2
-- title:
--   Hol Hom: val R res
-- statement:
--   The Hol Hom construction uses the val R res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L38-L42

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

theorem GlobalTheory.HolHom.valR_res (x : Sp A ⟶ X) {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    valR x V ((X.presheaf.map (homOfLE h).op).hom f) = valR x U f := by sorry
