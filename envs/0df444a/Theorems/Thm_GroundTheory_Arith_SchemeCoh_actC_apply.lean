-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_actC_apply
-- name    : GroundTheory.Arith.SchemeCoh.actC_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:49.569654+00:00
-- url     : https://prove2.me/theorems/6c8e13c3-e79e-4300-91ad-13cd02bcad7f
-- title:
--   Scheme Coh: act C apply
-- statement:
--   The Scheme Coh construction uses the act C apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L71-L72

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {R : Type u} [CommRing R]
variable {D : R → Opens X} (A : LocalizingAction P D)
variable {ι : Type u} (U : ι → Opens X)

theorem GroundTheory.Arith.SchemeCoh.actC_apply (r : R) (n : ℕ) (σ : Cochain P U n) (i : Fin (n + 1) → ι) :
    actC A U r n σ i = A.act r _ (σ i) := by sorry
