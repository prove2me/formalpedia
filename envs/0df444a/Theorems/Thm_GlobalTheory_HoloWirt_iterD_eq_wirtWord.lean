-- Prove2me | Theorems.Thm_GlobalTheory_HoloWirt_iterD_eq_wirtWord
-- name    : GlobalTheory.HoloWirt.iterD_eq_wirtWord
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:06.621837+00:00
-- url     : https://prove2.me/theorems/1f1127bf-54dd-4f2f-9e22-3a32a1a43cf1
-- title:
--   Holo Wirt: iter D eq wirt Word
-- statement:
--   The Holo Wirt construction uses the iter D eq wirt Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedComplexPartialDerivativeEqWirtingerWord.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedComplexPartialDerivativeEqWirtingerWord.lean#L66-L70

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

theorem GlobalTheory.HoloWirt.iterD_eq_wirtWord : ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ g U → ∀ (l : List I), ∀ z ∈ U,
      iterD l g z = wirtWord (l.map fun i => (i, false)) g z := by sorry
