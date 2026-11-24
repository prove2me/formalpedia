-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_PairClass_exists_aeval_eq_of_separable
-- name    : GlobalTheory.UnitLemma.PairClass.exists_aeval_eq_of_separable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:36:48.32179+00:00
-- url     : https://prove2.me/theorems/077ae209-fb75-4897-91c6-f07a5acfe83c
-- title:
--   Pair Class: exists aeval eq of separable
-- statement:
--   The Pair Class construction uses the exists aeval eq of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfSeparable.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfSeparable.lean#L9-L28

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

theorem GlobalTheory.UnitLemma.PairClass.exists_aeval_eq_of_separable {F A : Type} [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (a : A) (hs : (LinearMap.mulLeft F a).charpoly.Separable) (y : A) :
    ∃ q : F[X], y = aeval a q := by sorry
