-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_PairClass_trace_nondeg
-- name    : GlobalTheory.UnitLemma.PairClass.trace_nondeg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:37:11.935994+00:00
-- url     : https://prove2.me/theorems/09dd8fc5-8183-433e-9cac-93bb6ec25df9
-- title:
--   Pair Class: trace nondeg
-- statement:
--   The Pair Class construction uses the trace nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfSeparable.lean#L38-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfSeparable.lean#L38-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PairClass

theorem GlobalTheory.UnitLemma.PairClass.trace_nondeg (F A : Type) [Field F] [CharZero F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (a : A) (hs : (LinearMap.mulLeft F a).charpoly.Separable) (x : A)
    (hx : ∀ y, Algebra.trace F A (x * y) = 0) : x = 0 := by sorry
