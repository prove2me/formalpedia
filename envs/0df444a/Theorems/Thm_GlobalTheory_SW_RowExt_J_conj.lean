-- Prove2me | Theorems.Thm_GlobalTheory_SW_RowExt_J_conj
-- name    : GlobalTheory.SW.RowExt.J_conj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:44:29.266907+00:00
-- url     : https://prove2.me/theorems/4fe71083-1063-480e-992f-0da1c550d7b5
-- title:
--   Row Ext: J conj
-- statement:
--   The Row Ext construction uses the J conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitaryExt.lean#L96-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitaryExt.lean#L96-L97

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

theorem GlobalTheory.SW.RowExt.J_conj [DecidableEq α] : (Matrix.J α E)ᴴ = -Matrix.J α E := by sorry
