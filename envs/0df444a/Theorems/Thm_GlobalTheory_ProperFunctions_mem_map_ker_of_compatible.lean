-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_ker_of_compatible
-- name    : GlobalTheory.ProperFunctions.mem_map_ker_of_compatible
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:56:28.621695+00:00
-- url     : https://prove2.me/theorems/f4391bd6-c6ef-4e87-814d-0d8e6bde3770
-- title:
--   Proper Functions: mem map ker of compatible
-- statement:
--   The Proper Functions construction uses the mem map ker of compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L200-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L200-L287

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

theorem GlobalTheory.ProperFunctions.mem_map_ker_of_compatible {Y T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S}
    {q : Y ⟶ T} (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat p] (t : T)
    [Subsingleton T]
    (hq : Function.Surjective q.appTop) {e : S ⟶ X} (he : e ≫ p = 𝟙 S)
    (h : ∀ U : X.affineOpens, Γ(X, U.1))
    (hc : ∀ (U V : X.affineOpens) (hVU : V.1 ≤ U.1),
      X.presheaf.map (homOfLE hVU).op (h U) - h V ∈
        (RingHom.ker f.appTop.hom).map (p.appLE ⊤ V.1 (le_preimage_top p _)).hom)
    (hv : ∀ (U : X.affineOpens) (W : S.affineOpens) (hW : W.1 ≤ e ⁻¹ᵁ U.1),
      e.appLE U.1 W.1 hW (h U) ∈ (RingHom.ker f.appTop.hom).map
        (Scheme.Hom.appLE (𝟙 S) ⊤ W.1 (le_preimage_top _ _)).hom)
    (U : X.affineOpens) :
    h U ∈ (RingHom.ker f.appTop.hom).map (p.appLE ⊤ U.1 (le_preimage_top p _)).hom := by sorry
