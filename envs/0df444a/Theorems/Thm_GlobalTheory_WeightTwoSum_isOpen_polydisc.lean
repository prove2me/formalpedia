-- Prove2me | Theorems.Thm_GlobalTheory_WeightTwoSum_isOpen_polydisc
-- name    : GlobalTheory.WeightTwoSum.isOpen_polydisc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:51:38.115397+00:00
-- url     : https://prove2.me/theorems/16e50150-b4f0-435c-9f99-01a9287dd9db
-- title:
--   Weight Two Sum: is Open polydisc
-- statement:
--   The Weight Two Sum construction uses the is Open polydisc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableRisingS.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableRisingS.lean#L53-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped ContDiff
open GlobalTheory GlobalTheory.WeightTwoSum
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem GlobalTheory.WeightTwoSum.isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by sorry
