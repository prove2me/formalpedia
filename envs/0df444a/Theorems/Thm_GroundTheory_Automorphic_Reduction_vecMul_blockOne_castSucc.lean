-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_vecMul_blockOne_castSucc
-- name    : GroundTheory.Automorphic.Reduction.vecMul_blockOne_castSucc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:00.080329+00:00
-- url     : https://prove2.me/theorems/bec0e80f-227b-433c-b762-43e62b9c125f
-- title:
--   Reduction: vec Mul block One cast Succ
-- statement:
--   The Reduction construction uses the vec Mul block One cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionBlock.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionBlock.lean#L67-L69

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Reduction
variable {R : Type*} [CommRing R] {m : ℕ}

theorem GroundTheory.Automorphic.Reduction.vecMul_blockOne_castSucc (y : Fin (m + 1) → R) (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    (y ᵥ* blockOne M) (Fin.castSucc j) = (Fin.init y ᵥ* M) j := by sorry
