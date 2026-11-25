-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_of_flat_of_map_maximalIdeal
-- name    : GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:45.354481+00:00
-- url     : https://prove2.me/theorems/28743fde-df01-44ce-902d-be8c463c5a1f
-- title:
--   Is Regular Local Ring: of flat of map maximal Ideal
-- statement:
--   The Is Regular Local Ring construction uses the of flat of map maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L23-L33

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
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
open IsLocalRing
universe u

theorem GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] [IsRegularLocalRing A]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) : IsRegularLocalRing B := by sorry
