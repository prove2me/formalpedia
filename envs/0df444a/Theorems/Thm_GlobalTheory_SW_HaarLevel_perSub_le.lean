-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarLevel_perSub_le
-- name    : GlobalTheory.SW.HaarLevel.perSub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:48.445194+00:00
-- url     : https://prove2.me/theorems/36cfc81f-36c1-4868-a738-2d6b216d9ab3
-- title:
--   Haar Level: per Sub le
-- statement:
--   The Haar Level construction uses the per Sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L98-L101

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

theorem GlobalTheory.SW.HaarLevel.perSub_le (R S : ℕ) : perSub K κ ι (R * S) ≤ perSub K κ ι R := by sorry
