-- Prove2me | Theorems.Thm_GlobalTheory_SW_SiegelSum_exists_int_of_intM
-- name    : GlobalTheory.SW.SiegelSum.exists_int_of_intM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:19.889805+00:00
-- url     : https://prove2.me/theorems/3c36ef2c-eeb4-4e67-81b6-446e7b766d2e
-- title:
--   Siegel Sum: exists int of int M
-- statement:
--   The Siegel Sum construction uses the exists int of int M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableNormSiegelThetaSeriesTerms.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableNormSiegelThetaSeriesTerms.lean#L54-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableProdPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SiegelSum

theorem GlobalTheory.SW.SiegelSum.exists_int_of_intM {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (hR : 0 < R)
    {x : Matrix κ ι ℚ} (hx : IntM ((R : ℚ) • x)) :
    ∃ n : κ → ι → ℤ, x = Matrix.of fun k i => (n k i : ℚ) / R := by sorry
