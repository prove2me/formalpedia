-- Prove2me | Theorems.Thm_GlobalTheory_DualFibreRank_cmp_bijective
-- name    : GlobalTheory.DualFibreRank.cmp_bijective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:51:30.468794+00:00
-- url     : https://prove2.me/theorems/dbbe19d9-fcd7-472a-8692-9893a8c1de8e
-- title:
--   Dual Fibre Rank: cmp bijective
-- statement:
--   The Dual Fibre Rank construction uses the cmp bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankDualAndRangeDualMapBaseChange.lean#L36-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankDualAndRangeDualMapBaseChange.lean#L36-L56

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

theorem GlobalTheory.DualFibreRank.cmp_bijective [Module.Projective O M] [Module.Finite O M] :
    Function.Bijective (cmp A M (O := O)) := by sorry
