-- Prove2me | Theorems.Thm_GlobalTheory_PairOp_unit_FFStar_FF
-- name    : GlobalTheory.PairOp.unit_FFStar_FF
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:12.333154+00:00
-- url     : https://prove2.me/theorems/595526b4-0a1a-4106-8773-76cd10417e36
-- title:
--   Pair Op: unit FFStar FF
-- statement:
--   The Pair Op construction uses the unit FFStar FF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L448-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L448-L450

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
variable (χ)

theorem GlobalTheory.PairOp.unit_FFStar_FF (c : 𝓀[k]ˣ) :
    (dia c * FFStar q χ * (dia c⁻¹ * FF q χ) : Module.End ℂ (Form k n M)) = FFStar q χ * FF q χ := by sorry
