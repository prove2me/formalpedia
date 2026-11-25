-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_one
-- name    : GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:11.345376+00:00
-- url     : https://prove2.me/theorems/d58090e1-378d-46bb-8a5a-b25b829b8ce4
-- title:
--   Is Regular Local Ring: unique Factorization Monoid of ring Krull Dim le one
-- statement:
--   The Is Regular Local Ring construction uses the unique Factorization Monoid of ring Krull Dim le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularCurve.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularCurve.lean#L26-L30

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
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

theorem GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_one {R : Type*}
    [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : UniqueFactorizationMonoid R := by sorry
