-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_IsRightAct_algOp_mul
-- name    : GlobalTheory.LevDesc.IsRightAct.algOp_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:11.926172+00:00
-- url     : https://prove2.me/theorems/120493f0-7301-53e2-ab85-b0aacffc609f
-- title:
--   Is Right Act: alg Op mul
-- statement:
--   The Is Right Act construction uses the alg Op mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L90-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]
variable (st : G → R →ₐ[K] R)

theorem GlobalTheory.LevDesc.IsRightAct.algOp_mul {st : G → R →ₐ[K] R} (hs : IsRightAct st) (e e' : MonoidAlgebra K G) :
    algOp st (e * e') = algOp st e * algOp st e' := by sorry
