-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_pow_mul_pow
-- name    : GlobalTheory.LatClass.pow_mul_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:31.438979+00:00
-- url     : https://prove2.me/theorems/d4e1b37e-4715-4b45-8bd8-09efc8d2c013
-- title:
--   Lat Class: pow mul pow
-- statement:
--   The Lat Class construction uses the pow mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L27-L30

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

theorem GlobalTheory.LatClass.pow_mul_pow {a b : ℤ} {t s : k} (ht : t ∈ powInt ϖ a) (hs : s ∈ powInt ϖ b) : t * s ∈ powInt ϖ (a + b) := by sorry
