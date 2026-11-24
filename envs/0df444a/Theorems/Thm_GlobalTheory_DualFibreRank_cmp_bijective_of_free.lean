-- Prove2me | Theorems.Thm_GlobalTheory_DualFibreRank_cmp_bijective_of_free
-- name    : GlobalTheory.DualFibreRank.cmp_bijective_of_free
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:51:20.700005+00:00
-- url     : https://prove2.me/theorems/91c1e87f-01ab-4592-a065-47f7c23d4cf6
-- title:
--   Dual Fibre Rank: cmp bijective of free
-- statement:
--   The Dual Fibre Rank construction uses the cmp bijective of free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankDualAndRangeDualMapBaseChange.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankDualAndRangeDualMapBaseChange.lean#L25-L34

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

theorem GlobalTheory.DualFibreRank.cmp_bijective_of_free [Module.Free O M] [Module.Finite O M] :
    Function.Bijective (cmp A M (O := O)) := by sorry
