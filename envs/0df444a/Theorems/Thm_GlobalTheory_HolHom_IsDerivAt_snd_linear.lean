-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_snd_linear
-- name    : GlobalTheory.HolHom.IsDerivAt.snd_linear
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:36:17.21712+00:00
-- url     : https://prove2.me/theorems/d6ad6e39-b6c9-443a-bddc-4c0cd061028c
-- title:
--   Is Deriv At: snd linear
-- statement:
--   The Is Deriv At construction uses the snd linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L470-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L470-L474

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.HolHom.IsDerivAt.snd_linear {X : Scheme.{0}} {c : V → (Sp ℂ ⟶ X)} {z w₁ w₂ : V} {a₁ a₂ : ℂ}
    {v₁ v₂ v : Sp (DualNumber ℂ) ⟶ X} (h₁ : IsDerivAt c z w₁ v₁) (h₂ : IsDerivAt c z w₂ v₂)
    (h : IsDerivAt c z (a₁ • w₁ + a₂ • w₂) v) (U : X.Opens) (hU : ⊤ ≤ c z ⁻¹ᵁ U) (f : Γ(X, U)) :
    TrivSqZeroExt.snd (valR v U f) = a₁ * TrivSqZeroExt.snd (valR v₁ U f) + a₂ * TrivSqZeroExt.snd (valR v₂ U f) := by sorry
