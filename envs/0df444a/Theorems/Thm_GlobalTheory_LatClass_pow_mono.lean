-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_pow_mono
-- name    : GlobalTheory.LatClass.pow_mono
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:48.230205+00:00
-- url     : https://prove2.me/theorems/3006a141-0ffb-549a-a825-e9e66dbbe823
-- title:
--   Lat Class: pow mono
-- statement:
--   The Lat Class construction uses the pow mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L38-L42

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

theorem GlobalTheory.LatClass.pow_mono {a b : ℤ} (h : a ≤ b) {s : k} (hs : s ∈ powInt ϖ b) : s ∈ powInt ϖ a := by sorry
