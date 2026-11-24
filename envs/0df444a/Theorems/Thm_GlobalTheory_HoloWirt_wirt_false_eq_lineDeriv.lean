-- Prove2me | Theorems.Thm_GlobalTheory_HoloWirt_wirt_false_eq_lineDeriv
-- name    : GlobalTheory.HoloWirt.wirt_false_eq_lineDeriv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:38.430431+00:00
-- url     : https://prove2.me/theorems/843a5eb2-a049-4bb6-aa8a-bf1c31f87633
-- title:
--   Holo Wirt: wirt false eq line Deriv
-- statement:
--   The Holo Wirt construction uses the wirt false eq line Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedComplexPartialDerivativeEqWirtingerWord.lean#L19-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedComplexPartialDerivativeEqWirtingerWord.lean#L19-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedComplexPartialDerivativeEqWirtingerWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.HoloWirt

theorem GlobalTheory.HoloWirt.wirt_false_eq_lineDeriv {I : Type} [Fintype I] [DecidableEq I] (i : I) (h : (I → ℂ) → ℂ) (z : I → ℂ)
    (hd : DifferentiableAt ℂ h z) : wirt i false h z = lineDeriv ℂ h z (Pi.single i 1) := by sorry
