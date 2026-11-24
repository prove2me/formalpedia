-- Prove2me | Theorems.Thm_GlobalTheory_DualFibreRank_cmp_natural_apply
-- name    : GlobalTheory.DualFibreRank.cmp_natural_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:51:31.582716+00:00
-- url     : https://prove2.me/theorems/d8b3eb21-2ae0-426a-98da-82045cbf36fa
-- title:
--   Dual Fibre Rank: cmp natural apply
-- statement:
--   The Dual Fibre Rank construction uses the cmp natural apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankDualAndRangeDualMapBaseChange.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankDualAndRangeDualMapBaseChange.lean#L21-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.DualFibreRank
variable {O : Type} [CommRing O] (A : Type) [CommRing A] [Algebra O A]
variable {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]

theorem GlobalTheory.DualFibreRank.cmp_natural_apply (f : M →ₗ[O] N) (x : A ⊗[O] Module.Dual O N) :
    cmp A M (f.dualMap.baseChange A x) = (f.baseChange A).dualMap (cmp A N x) := by sorry
