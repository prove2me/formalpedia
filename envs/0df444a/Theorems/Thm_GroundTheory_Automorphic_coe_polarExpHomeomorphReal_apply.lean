-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_coe_polarExpHomeomorphReal_apply
-- name    : GroundTheory.Automorphic.coe_polarExpHomeomorphReal_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:29.439398+00:00
-- url     : https://prove2.me/theorems/23f9f678-9f12-5668-9e02-bd23c42d0940
-- title:
--   Automorphic: coe polar Exp Homeomorph Real apply
-- statement:
--   The Automorphic construction uses the coe polar Exp Homeomorph Real apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsPolar.lean#L174-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsPolar.lean#L174-L177

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem GroundTheory.Automorphic.coe_polarExpHomeomorphReal_apply
    (kX : unitaryGroup n ℝ × {X : Matrix n n ℝ // X.IsHermitian}) :
    ((polarExpHomeomorphReal kX : GL n ℝ) : Matrix n n ℝ) = kX.1 * NormedSpace.exp kX.2.1 := by sorry
