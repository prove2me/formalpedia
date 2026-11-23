-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_valR_spMap
-- name    : GlobalTheory.HolHom.valR_spMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:46:39.60977+00:00
-- url     : https://prove2.me/theorems/4039cdcd-4361-436b-9e37-92f6e4009a36
-- title:
--   Hol Hom: val R sp Map
-- statement:
--   The Hol Hom construction uses the val R sp Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L44-L52

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

theorem GlobalTheory.HolHom.valR_spMap {A' : Type} [CommRing A'] (ρ : A →+* A') (x : Sp A ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR (spMap ρ ≫ x) U f = ρ (valR x U f) := by sorry
