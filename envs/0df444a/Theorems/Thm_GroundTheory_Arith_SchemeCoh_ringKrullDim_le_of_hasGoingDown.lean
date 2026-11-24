-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ringKrullDim_le_of_hasGoingDown
-- name    : GroundTheory.Arith.SchemeCoh.ringKrullDim_le_of_hasGoingDown
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:49.185435+00:00
-- url     : https://prove2.me/theorems/ef12c178-3f07-4628-bfb0-13e54653e502
-- title:
--   Scheme Coh: ring Krull Dim le of has Going Down
-- statement:
--   The Scheme Coh construction uses the ring Krull Dim le of has Going Down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularSmooth.lean#L11-L21

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

theorem GroundTheory.Arith.SchemeCoh.ringKrullDim_le_of_hasGoingDown {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Algebra.HasGoingDown A B] :
    ringKrullDim A ≤ ringKrullDim B := by sorry
