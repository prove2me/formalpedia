-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernel_extZero_of_isRegularLocalRing
-- name    : GlobalTheory.DualCokernel.extZero_of_isRegularLocalRing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:47.962408+00:00
-- url     : https://prove2.me/theorems/d9c60ad9-fa6b-493a-b19a-af00d87ca3d5
-- title:
--   Dual Cokernel: ext Zero of is Regular Local Ring
-- statement:
--   The Dual Cokernel construction uses the ext Zero of is Regular Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExactDualMapOfExactFibresOfIsRegularLocalRing.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExactDualMapOfExactFibresOfIsRegularLocalRing.lean#L9-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernel

theorem GlobalTheory.DualCokernel.extZero_of_isRegularLocalRing (R : Type) [CommRing R] [IsRegularLocalRing R] (g : ℕ)
    (hg : ringKrullDim R = g) (j : ℕ) (hj : j < g) : ExtZero (R := R) R j := by sorry
