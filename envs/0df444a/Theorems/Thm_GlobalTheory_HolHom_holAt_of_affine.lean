-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_holAt_of_affine
-- name    : GlobalTheory.HolHom.holAt_of_affine
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:09:53.632216+00:00
-- url     : https://prove2.me/theorems/731f5848-0d76-4bda-bba6-eea8ea599b1c
-- title:
--   Hol Hom: hol At of affine
-- statement:
--   The Hol Hom construction uses the hol At of affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L137-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L137-L159

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

theorem GlobalTheory.HolHom.holAt_of_affine {c : V → (Sp ℂ ⟶ X)} {z : V} {P : X.Opens} (hP : IsAffineOpen P) (h₀ : ⊤ ≤ c z ⁻¹ᵁ P)
    (hev : ∀ᶠ t in 𝓝 z, ⊤ ≤ c t ⁻¹ᵁ P) (hd : ∀ g : Γ(X, P), DifferentiableAt ℂ (fun t => valAt' (c t) P g) z) :
    HolAt c z := by sorry
