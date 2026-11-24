-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isPrincipalIdealRing_of_ringKrullDim_le_one
-- name    : GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:06.051831+00:00
-- url     : https://prove2.me/theorems/c8392362-aeb2-48fd-bd5e-dc907646dc86
-- title:
--   Is Regular Local Ring: is Principal Ideal Ring of ring Krull Dim le one
-- statement:
--   The Is Regular Local Ring construction uses the is Principal Ideal Ring of ring Krull Dim le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularCurve.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularCurve.lean#L11-L24

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

theorem GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : IsPrincipalIdealRing R := by sorry
