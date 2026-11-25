-- Prove2me | Theorems.Thm_GlobalTheory_CycInvariants_stabilizer_finiteIndex
-- name    : GlobalTheory.CycInvariants.stabilizer_finiteIndex
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:07:50.936014+00:00
-- url     : https://prove2.me/theorems/bacbd1f1-7261-4a03-aa0e-3bc470e0fffa
-- title:
--   Cyc Invariants: stabilizer finite Index
-- statement:
--   The Cyc Invariants construction uses the stabilizer finite Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerFixedIffMemCompletedIntegers.lean#L46-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerFixedIffMemCompletedIntegers.lean#L46-L58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerTraceAlmostSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumMulLeftTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycInvariants
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.CycInvariants.stabilizer_finiteIndex (x : Om l) : (MulAction.stabilizer (GQ l) x).FiniteIndex := by sorry
