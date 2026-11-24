-- Prove2me | Theorems.Thm_GlobalTheory_UnitVectorStabiliser_restrHom_surjective
-- name    : GlobalTheory.UnitVectorStabiliser.restrHom_surjective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:38:47.964771+00:00
-- url     : https://prove2.me/theorems/b9ebadff-ebe6-484e-ae78-136bdf7e75a1
-- title:
--   Unit Vector Stabiliser: restr Hom surjective
-- statement:
--   The Unit Vector Stabiliser construction uses the restr Hom surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L193-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L193-L220

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

theorem GlobalTheory.UnitVectorStabiliser.restrHom_surjective (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v)
    (hx : IsUnit (hR (Fv F v) σ J x x)) :
    Function.Surjective (restrHom σ J v (perpLat σ J v L x) x) := by sorry
