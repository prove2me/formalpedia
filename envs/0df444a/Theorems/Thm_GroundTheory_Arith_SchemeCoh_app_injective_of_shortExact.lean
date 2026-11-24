-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_injective_of_shortExact
-- name    : GroundTheory.Arith.SchemeCoh.app_injective_of_shortExact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:04.287281+00:00
-- url     : https://prove2.me/theorems/5841501b-e394-41a8-9d02-e2f2116846c1
-- title:
--   Scheme Coh: app injective of short Exact
-- statement:
--   The Scheme Coh construction uses the app injective of short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L124-L127

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

theorem GroundTheory.Arith.SchemeCoh.app_injective_of_shortExact (W : (Opens X)ᵒᵖ) : Function.Injective (S.f.hom.app W) := by sorry
