-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_IsRightAct_algOp_eq
-- name    : GlobalTheory.LevDesc.IsRightAct.algOp_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:02:07.678584+00:00
-- url     : https://prove2.me/theorems/25aa859d-6d71-4b97-b627-55d847119930
-- title:
--   Is Right Act: alg Op eq
-- statement:
--   The Is Right Act construction uses the alg Op eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L83-L88

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

theorem GlobalTheory.LevDesc.IsRightAct.algOp_eq {st : G → R →ₐ[K] R} (hs : IsRightAct st) (e : MonoidAlgebra K G) :
    algOp st e = hs.leftRep.asAlgebraHom e := by sorry
