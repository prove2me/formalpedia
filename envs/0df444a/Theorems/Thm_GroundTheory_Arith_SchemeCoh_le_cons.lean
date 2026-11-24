-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_le_cons
-- name    : GroundTheory.Arith.SchemeCoh.le_cons
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:55.492592+00:00
-- url     : https://prove2.me/theorems/e34b97a1-25ce-414b-9ddc-8ed8dee00937
-- title:
--   Scheme Coh: le cons
-- statement:
--   The Scheme Coh construction uses the le cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L79-L84

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

theorem GroundTheory.Arith.SchemeCoh.le_cons {n : ℕ} (j : ι) (I : Fin (n + 1) → ι) :
    inter U (Fin.cons j I : Fin (n + 2) → ι) ≤ inter U I := by sorry
