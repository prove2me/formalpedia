-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarLevel_index_nsmul
-- name    : GlobalTheory.SW.HaarLevel.index_nsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:21.499062+00:00
-- url     : https://prove2.me/theorems/54c64744-951a-4a6b-8bfa-f9ce3f770b3e
-- title:
--   Haar Level: index nsmul
-- statement:
--   The Haar Level construction uses the index nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L76-L79

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

theorem GlobalTheory.SW.HaarLevel.index_nsmul (R : ℕ) : (nsmulAddMonoidHom R : Matrix κ ι (𝓞 K) →+ _).range.index =
    R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) := by sorry
