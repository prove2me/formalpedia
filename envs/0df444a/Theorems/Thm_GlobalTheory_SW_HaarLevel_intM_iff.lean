-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarLevel_intM_iff
-- name    : GlobalTheory.SW.HaarLevel.intM_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:00.753509+00:00
-- url     : https://prove2.me/theorems/c315f7ab-3a95-43a4-8268-f3e286cc72db
-- title:
--   Haar Level: int M iff
-- statement:
--   The Haar Level construction uses the int M iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L45-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
omit [NumberField K] [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.HaarLevel.intM_iff (x : Matrix κ ι K) : IntM x ↔ ∃ y, incl K κ ι y = x := by sorry
