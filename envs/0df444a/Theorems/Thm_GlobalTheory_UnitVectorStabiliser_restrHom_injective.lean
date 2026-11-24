-- Prove2me | Theorems.Thm_GlobalTheory_UnitVectorStabiliser_restrHom_injective
-- name    : GlobalTheory.UnitVectorStabiliser.restrHom_injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:24.258465+00:00
-- url     : https://prove2.me/theorems/bd5eb0d4-34cd-4001-8b83-a1fb3c902655
-- title:
--   Unit Vector Stabiliser: restr Hom injective
-- statement:
--   The Unit Vector Stabiliser construction uses the restr Hom injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L173-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L173-L191

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

theorem GlobalTheory.UnitVectorStabiliser.restrHom_injective (L' : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v)
    (hx : IsUnit (hR (Fv F v) σ J x x)) : Function.Injective (restrHom σ J v L' x) := by sorry
