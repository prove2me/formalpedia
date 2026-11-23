-- Prove2me | Theorems.Thm_GlobalTheory_SW_HAct_ccT_mul
-- name    : GlobalTheory.SW.HAct.ccT_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:40.160107+00:00
-- url     : https://prove2.me/theorems/58bbb0d2-99db-4331-80e2-e477d8f26e7f
-- title:
--   HAct: cc T mul
-- statement:
--   The HAct construction uses the cc T mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L120-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mul

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem GlobalTheory.SW.HAct.ccT_mul {α β δ : Type} [Fintype β] (X : Matrix α β E) (Y : Matrix β δ E) :
    ccT (X * Y) = ccT Y * ccT X := by sorry
