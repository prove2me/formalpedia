-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_zpow_mem_pow
-- name    : GlobalTheory.LatClass.zpow_mem_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:46:45.570258+00:00
-- url     : https://prove2.me/theorems/91680cef-194a-46c6-b1a7-dc811b98341a
-- title:
--   Lat Class: zpow mem pow
-- statement:
--   The Lat Class construction uses the zpow mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L35-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hϖ : valuation k (ϖ : k) = uniformizer k)
include hϖ

theorem GlobalTheory.LatClass.zpow_mem_pow {a b : ℤ} : (ϖ : k) ^ a ∈ powInt ϖ b ↔ b ≤ a := by sorry
