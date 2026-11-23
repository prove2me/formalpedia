-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarLevel_mem_perSub
-- name    : GlobalTheory.SW.HaarLevel.mem_perSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:06.729466+00:00
-- url     : https://prove2.me/theorems/0b680298-673a-41af-b0cf-3ca8d350b947
-- title:
--   Haar Level: mem per Sub
-- statement:
--   The Haar Level construction uses the mem per Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L71-L74

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

theorem GlobalTheory.SW.HaarLevel.mem_perSub (R : ℕ) (x : Matrix κ ι K) :
    x ∈ perSub K κ ι R ↔ ∃ y, R • incl K κ ι y = x := by sorry
