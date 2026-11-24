-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_injectiveSequence_shortExact
-- name    : GroundTheory.Arith.SchemeCoh.injectiveSequence_shortExact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:37.595142+00:00
-- url     : https://prove2.me/theorems/e9e33ca4-b2b7-49aa-a47c-618a4c63fdf6
-- title:
--   Scheme Coh: injective Sequence short Exact
-- statement:
--   The Scheme Coh construction uses the injective Sequence short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechToDerived.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechToDerived.lean#L17-L21

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived
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
open CategoryTheory Opposite TopologicalSpace Limits Abelian
universe w' u
variable {X : TopCat.{u}} {B : Opens X → Prop}

theorem GroundTheory.Arith.SchemeCoh.injectiveSequence_shortExact (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (injectiveSequence F).ShortExact := by sorry
