-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_existsUnique_hom_app_top
-- name    : GroundTheory.Arith.Etale.existsUnique_hom_app_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:26:43.341212+00:00
-- url     : https://prove2.me/theorems/60efddb9-1872-4fa8-aca1-96114e29f067
-- title:
--   Etale: exists Unique hom app top
-- statement:
--   The Etale construction uses the exists Unique hom app top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L76-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L76-L93

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false

theorem GroundTheory.Arith.Etale.existsUnique_hom_app_top {A : CommRingCat.{u}} (P P' : (Spec A).Modules)
    [IsIso P.fromTildeΓ] (f : Γ(P, ⊤) →ₗ[Γ(Spec A, ⊤)] Γ(P', ⊤)) :
    ∃! θ : P ⟶ P', ∀ x, θ.app ⊤ x = f x := by sorry
