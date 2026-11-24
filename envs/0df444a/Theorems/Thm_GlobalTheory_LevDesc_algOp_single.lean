-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_algOp_single
-- name    : GlobalTheory.LevDesc.algOp_single
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:02:13.508258+00:00
-- url     : https://prove2.me/theorems/3a932f4b-563c-499e-83e3-fc8fc6f2266d
-- title:
--   Lev Desc: alg Op single
-- statement:
--   The Lev Desc construction uses the alg Op single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L74-L75

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

theorem GlobalTheory.LevDesc.algOp_single (g : G) (a : K) (x : R) : algOp st (MonoidAlgebra.single g a) x = a • st g⁻¹ x := by sorry
