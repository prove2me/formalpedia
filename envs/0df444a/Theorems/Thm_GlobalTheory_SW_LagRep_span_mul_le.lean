-- Prove2me | Theorems.Thm_GlobalTheory_SW_LagRep_span_mul_le
-- name    : GlobalTheory.SW.LagRep.span_mul_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:35.570287+00:00
-- url     : https://prove2.me/theorems/1cb86f2a-c8b0-4bc5-9714-d0afadbacf9f
-- title:
--   Lag Rep: span mul le
-- statement:
--   The Lag Rep construction uses the span mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LinearIndependentMul.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LinearIndependentMul.lean#L25-L36

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

theorem GlobalTheory.SW.LagRep.span_mul_le {E κ ι : Type} [Field E] [Fintype κ]
    (b : Matrix κ κ E) (W : Matrix κ ι E) :
    Submodule.span E (Set.range fun i => (b * W) i) ≤
      Submodule.span E (Set.range fun i => W i) := by sorry
