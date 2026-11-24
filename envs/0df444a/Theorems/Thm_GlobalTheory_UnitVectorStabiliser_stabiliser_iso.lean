-- Prove2me | Theorems.Thm_GlobalTheory_UnitVectorStabiliser_stabiliser_iso
-- name    : GlobalTheory.UnitVectorStabiliser.stabiliser_iso
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:21.186795+00:00
-- url     : https://prove2.me/theorems/1e686d1c-d1ce-477e-913b-df2e7f7a773b
-- title:
--   Unit Vector Stabiliser: stabiliser iso
-- statement:
--   The Unit Vector Stabiliser construction uses the stabiliser iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L224-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L224-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabiliser

theorem GlobalTheory.UnitVectorStabiliser.stabiliser_iso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (OEv F E v) (Fin M → Ev F E v)), ∀ x : Fin M → Ev F E v, IsUnit (hR (Fv F v) σ J x x) → ∃ φ : (stabLat σ J v (perpLat σ J v L x) ⊓ stabVec σ J v x : Subgroup (HA (Fv F v) σ J)) ≃* unitaryLatIn σ J v (perp σ J v x) (perpLat σ J v L x), ∀ g (y : perp σ J v x), (((φ g : perp σ J v x ≃ₗ[Ev F E v] perp σ J v x) y : perp σ J v x) : Fin M → Ev F E v) = act σ J v (g : HA (Fv F v) σ J) y := by sorry
