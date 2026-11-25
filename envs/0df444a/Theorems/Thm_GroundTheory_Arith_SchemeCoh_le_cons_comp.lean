-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_le_cons_comp
-- name    : GroundTheory.Arith.SchemeCoh.le_cons_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:20.177387+00:00
-- url     : https://prove2.me/theorems/f8513841-4e64-4047-b820-af6ed0a7dedb
-- title:
--   Scheme Coh: le cons comp
-- statement:
--   The Scheme Coh construction uses the le cons comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L86-L90

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

theorem GroundTheory.Arith.SchemeCoh.le_cons_comp {n : ℕ} (j : ι) (J : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    inter U (Fin.cons j J : Fin (n + 3) → ι) ≤
      inter U (Fin.cons j (J ∘ k.succAbove) : Fin (n + 2) → ι) := by sorry
