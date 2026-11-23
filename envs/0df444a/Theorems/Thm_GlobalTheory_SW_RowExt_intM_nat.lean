-- Prove2me | Theorems.Thm_GlobalTheory_SW_RowExt_intM_nat
-- name    : GlobalTheory.SW.RowExt.intM_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:15.590049+00:00
-- url     : https://prove2.me/theorems/2578a509-54ac-4821-a775-40e89af28fe9
-- title:
--   Row Ext: int M nat
-- statement:
--   The Row Ext construction uses the int M nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitaryExt.lean#L88-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitaryExt.lean#L88-L89

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

theorem GlobalTheory.SW.RowExt.intM_nat {A : Matrix α β E} (n : ℕ) (hA : IntM A) : IntM ((n : E) • A) := by sorry
