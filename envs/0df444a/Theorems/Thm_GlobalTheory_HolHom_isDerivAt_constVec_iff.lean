-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_isDerivAt_constVec_iff
-- name    : GlobalTheory.HolHom.isDerivAt_constVec_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:15.748804+00:00
-- url     : https://prove2.me/theorems/88e6611b-82e3-4d58-aca9-eb5955e8833a
-- title:
--   Hol Hom: is Deriv At const Vec iff
-- statement:
--   The Hol Hom construction uses the is Deriv At const Vec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L261-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L261-L264

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

theorem GlobalTheory.HolHom.isDerivAt_constVec_iff {c : V → (Sp ℂ ⟶ X)} {z w : V} : IsDerivAt c z w (constVec (c z)) ↔
    ∀ U : X.Opens, ⊤ ≤ c z ⁻¹ᵁ U → ∀ f : Γ(X, U), fderiv ℂ (fun t => valAt' (c t) U f) z w = 0 := by sorry
