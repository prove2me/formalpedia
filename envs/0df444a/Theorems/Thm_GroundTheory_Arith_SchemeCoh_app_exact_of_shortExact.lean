-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_exact_of_shortExact
-- name    : GroundTheory.Arith.SchemeCoh.app_exact_of_shortExact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:06.52728+00:00
-- url     : https://prove2.me/theorems/cb389a08-720d-4ab4-9618-f651c30e6b6e
-- title:
--   Scheme Coh: app exact of short Exact
-- statement:
--   The Scheme Coh construction uses the app exact of short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L130-L132

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
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
open CategoryTheory Opposite TopologicalSpace Limits
universe w u
variable {X : TopCat.{u}}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)
variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
include hS

theorem GroundTheory.Arith.SchemeCoh.app_exact_of_shortExact (W : Opens X) (y : S.X₂.obj.obj (op W))
    (hy : S.g.hom.app (op W) y = 0) : ∃ x, S.f.hom.app (op W) x = y := by sorry
