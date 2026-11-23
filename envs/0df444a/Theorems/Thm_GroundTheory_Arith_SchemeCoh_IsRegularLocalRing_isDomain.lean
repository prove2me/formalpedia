-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isDomain
-- name    : GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:08.750807+00:00
-- url     : https://prove2.me/theorems/97fb3e82-c91b-4257-a4b6-504077207c4f
-- title:
--   Is Regular Local Ring: is Domain
-- statement:
--   The Is Regular Local Ring construction uses the is Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularLocalDomain.lean#L113-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularLocalDomain.lean#L113-L179

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
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
open IsLocalRing Ideal
universe u
variable {R : Type u} [CommRing R]

theorem GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain [IsRegularLocalRing R] : IsDomain R := by sorry
