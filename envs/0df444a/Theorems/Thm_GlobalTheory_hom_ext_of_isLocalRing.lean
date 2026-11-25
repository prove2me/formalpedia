-- Prove2me | Theorems.Thm_GlobalTheory_hom_ext_of_isLocalRing
-- name    : GlobalTheory.hom_ext_of_isLocalRing
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:42:41.852973+00:00
-- url     : https://prove2.me/theorems/b320d342-fdfb-48f8-b626-81417bedadd3
-- title:
--   Global Theory: hom ext of is Local Ring
-- statement:
--   The Global Theory construction uses the hom ext of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean#L43-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory

theorem GlobalTheory.hom_ext_of_isLocalRing {A : Type u} [CommRing A] {Y : Scheme.{u}}
    {f g : Spec (.of A) ⟶ Y}
    (h : ∀ (B : Type u) [CommRing B] [IsLocalRing B] (φ : A →+* B),
      Spec.map (CommRingCat.ofHom φ) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ g) : f = g := by sorry
