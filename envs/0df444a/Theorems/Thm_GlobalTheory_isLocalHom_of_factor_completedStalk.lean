-- Prove2me | Theorems.Thm_GlobalTheory_isLocalHom_of_factor_completedStalk
-- name    : GlobalTheory.isLocalHom_of_factor_completedStalk
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:16.178922+00:00
-- url     : https://prove2.me/theorems/247ee6c7-c6b9-53b0-81cb-ca3a246c1d41
-- title:
--   Global Theory: is Local Hom of factor completed Stalk
-- statement:
--   The Global Theory construction uses the is Local Hom of factor completed Stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L170-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L170-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}

theorem GlobalTheory.isLocalHom_of_factor_completedStalk {f : Spec (.of R) ⟶ X} {x : X}
    (hx : f (closedPoint R) = x) (hfg : (maximalIdeal (X.presheaf.stalk x)).FG)
    {ψ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →+* R}
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ fromSpecCompletedStalk X x = f) : IsLocalHom ψ := by sorry
