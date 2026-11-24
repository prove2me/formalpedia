-- Prove2me | Theorems.Thm_GlobalTheory_HoloWirt_iterD_holo_and_eq
-- name    : GlobalTheory.HoloWirt.iterD_holo_and_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:46.420915+00:00
-- url     : https://prove2.me/theorems/f8e32f3b-06bf-4ca5-8cb7-aa5855b4470b
-- title:
--   Holo Wirt: iter D holo and eq
-- statement:
--   The Holo Wirt construction uses the iter D holo and eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedComplexPartialDerivativeEqWirtingerWord.lean#L39-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedComplexPartialDerivativeEqWirtingerWord.lean#L39-L64

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

theorem GlobalTheory.HoloWirt.iterD_holo_and_eq {I : Type} [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ)
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (l : List I) :
    DifferentiableOn ℂ (iterD l g) U ∧ Set.EqOn (iterD l g) (wirtWord (l.map fun i => (i, false)) g) U := by sorry
