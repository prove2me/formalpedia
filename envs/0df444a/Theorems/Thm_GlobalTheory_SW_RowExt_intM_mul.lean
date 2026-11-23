-- Prove2me | Theorems.Thm_GlobalTheory_SW_RowExt_intM_mul
-- name    : GlobalTheory.SW.RowExt.intM_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:02.263818+00:00
-- url     : https://prove2.me/theorems/ba4bb2aa-86bd-4973-80f1-46fb4f511dfc
-- title:
--   Row Ext: int M mul
-- statement:
--   The Row Ext construction uses the int M mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitaryExt.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitaryExt.lean#L79-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.RowExt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {α β γ : Type}
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.SW.RowExt.intM_mul [Fintype β] {A : Matrix α β E} {B : Matrix β γ E} (hA : IntM A) (hB : IntM B) :
    IntM (A * B) := by sorry
