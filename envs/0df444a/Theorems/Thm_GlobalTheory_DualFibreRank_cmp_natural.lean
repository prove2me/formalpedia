-- Prove2me | Theorems.Thm_GlobalTheory_DualFibreRank_cmp_natural
-- name    : GlobalTheory.DualFibreRank.cmp_natural
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:23.850255+00:00
-- url     : https://prove2.me/theorems/67c18548-8f4c-417f-a914-64be2b18be0b
-- title:
--   Dual Fibre Rank: cmp natural
-- statement:
--   The Dual Fibre Rank construction uses the cmp natural property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankDualAndRangeDualMapBaseChange.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankDualAndRangeDualMapBaseChange.lean#L16-L19

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

theorem GlobalTheory.DualFibreRank.cmp_natural (f : M →ₗ[O] N) :
    cmp A M ∘ₗ f.dualMap.baseChange A = (f.baseChange A).dualMap ∘ₗ cmp A N := by sorry
