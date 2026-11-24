-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_PairClass_aeval_mulLeft_apply
-- name    : GlobalTheory.UnitLemma.PairClass.aeval_mulLeft_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:28:58.566935+00:00
-- url     : https://prove2.me/theorems/096a092e-9206-4672-8300-82c56e45933a
-- title:
--   Pair Class: aeval mul Left apply
-- statement:
--   The Pair Class construction uses the aeval mul Left apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfSeparable.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfSeparable.lean#L30-L36

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

theorem GlobalTheory.UnitLemma.PairClass.aeval_mulLeft_apply {F A : Type} [Field F] [CommRing A] [Algebra F A] (a : A) (p : F[X]) (z : A) :
    aeval (LinearMap.mulLeft F a) p z = aeval a p * z := by sorry
