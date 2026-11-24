-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_of_compatible
-- name    : GlobalTheory.ProperFunctions.mem_map_of_compatible
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:56:24.830994+00:00
-- url     : https://prove2.me/theorems/139354fc-2d37-4ff6-931c-bca31c12260c
-- title:
--   Proper Functions: mem map of compatible
-- statement:
--   The Proper Functions construction uses the mem map of compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L314-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L314-L390

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X S : Scheme.{u}}

theorem GlobalTheory.ProperFunctions.mem_map_of_compatible {p : X ⟶ S} [IsAffine S] [IsLocallyNoetherian S] [Flat p]
    (hq : ∀ s : S, Function.Surjective (p.fiberToSpecResidueField s).appTop)
    {e : S ⟶ X} (he : e ≫ p = 𝟙 S) (I : Ideal Γ(S, ⊤))
    (h : ∀ U : X.affineOpens, Γ(X, U.1))
    (hc : ∀ (U V : X.affineOpens) (hVU : V.1 ≤ U.1),
      X.presheaf.map (homOfLE hVU).op (h U) - h V ∈
        I.map (p.appLE ⊤ V.1 (le_preimage_top p _)).hom)
    (hv : ∀ (U : X.affineOpens) (W : S.affineOpens) (hW : W.1 ≤ e ⁻¹ᵁ U.1),
      e.appLE U.1 W.1 hW (h U) ∈ I.map
        (Scheme.Hom.appLE (𝟙 S) ⊤ W.1 (le_preimage_top _ _)).hom)
    (U : X.affineOpens) :
    h U ∈ I.map (p.appLE ⊤ U.1 (le_preimage_top p _)).hom := by sorry
