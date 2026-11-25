-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_actC
-- name    : GroundTheory.Arith.SchemeCoh.d_actC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:45.802229+00:00
-- url     : https://prove2.me/theorems/a6dee7c8-13c2-4c95-ba30-0dc14915f9d5
-- title:
--   Scheme Coh: d act C
-- statement:
--   The Scheme Coh construction uses the d act C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L74-L77

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

theorem GroundTheory.Arith.SchemeCoh.d_actC (r : R) (n : ℕ) (σ : Cochain P U n) :
    d P U n (actC A U r n σ) = actC A U r (n + 1) (d P U n σ) := by sorry
