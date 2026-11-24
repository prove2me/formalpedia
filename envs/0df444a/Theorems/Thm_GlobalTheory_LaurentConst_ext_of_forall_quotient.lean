-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_ext_of_forall_quotient
-- name    : GlobalTheory.LaurentConst.ext_of_forall_quotient
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:00:57.827082+00:00
-- url     : https://prove2.me/theorems/83324acb-ccf9-4f2f-8b0d-0f4cef6fb44c
-- title:
--   Laurent Const: ext of forall quotient
-- statement:
--   The Laurent Const construction uses the ext of forall quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L250-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L250-L269

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}

theorem GlobalTheory.LaurentConst.ext_of_forall_quotient {Y : Scheme.{0}} (p : Y ⟶ S) [IsSeparated p] {D : Type} [CommRing D]
    {a b : Spec (.of D) ⟶ Y} (hab : a ≫ p = b ≫ p) (I : ℕ → Ideal D) (hI : ⨅ n, I n = ⊥)
    (H : ∀ n, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I n))) ≫ a =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I n))) ≫ b) : a = b := by sorry
