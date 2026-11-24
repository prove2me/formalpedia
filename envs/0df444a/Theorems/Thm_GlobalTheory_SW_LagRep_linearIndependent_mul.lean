-- Prove2me | Theorems.Thm_GlobalTheory_SW_LagRep_linearIndependent_mul
-- name    : GlobalTheory.SW.LagRep.linearIndependent_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:30.225147+00:00
-- url     : https://prove2.me/theorems/75e78438-1983-44ef-a85d-aed7929f6bd6
-- title:
--   Lag Rep: linear Independent mul
-- statement:
--   The Lag Rep construction uses the linear Independent mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LinearIndependentMul.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LinearIndependentMul.lean#L13-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LinearIndependentMul
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LagRep

theorem GlobalTheory.SW.LagRep.linearIndependent_mul {E κ ι : Type} [Field E] [Fintype κ] [DecidableEq κ]
    (b : Matrix κ κ E) (hb : b.det ≠ 0) (W : Matrix κ ι E)
    (hW : LinearIndependent E (fun i => W i)) : LinearIndependent E (fun i => (b * W) i) := by sorry
