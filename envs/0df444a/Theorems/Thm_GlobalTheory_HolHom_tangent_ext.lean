-- Prove2me | Theorems.Thm_GlobalTheory_HolHom_tangent_ext
-- name    : GlobalTheory.HolHom.tangent_ext
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:38:22.862594+00:00
-- url     : https://prove2.me/theorems/9d04ec78-a2b6-403b-9cb6-5a97fdef6644
-- title:
--   Hol Hom: tangent ext
-- statement:
--   The Hol Hom construction uses the tangent ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L234-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L234-L241

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

theorem GlobalTheory.HolHom.tangent_ext {v v' : Sp (DualNumber ℂ) ⟶ X} {x : Sp ℂ ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x)
    (h' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' = x)
    (H : ∀ U : X.Opens, ⊤ ≤ x ⁻¹ᵁ U → ∀ f : Γ(X, U),
      TrivSqZeroExt.snd (valR v U f) = TrivSqZeroExt.snd (valR v' U f)) : v = v' := by sorry
