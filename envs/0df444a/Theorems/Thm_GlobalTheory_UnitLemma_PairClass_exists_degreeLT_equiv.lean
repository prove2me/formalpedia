-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_PairClass_exists_degreeLT_equiv
-- name    : GlobalTheory.UnitLemma.PairClass.exists_degreeLT_equiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:29:00.60536+00:00
-- url     : https://prove2.me/theorems/d4dd111f-ada8-4cc9-8cd9-8064705f9fc3
-- title:
--   Pair Class: exists degree LT equiv
-- statement:
--   The Pair Class construction uses the exists degree LT equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfSeparable.lean#L100-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfSeparable.lean#L100-L119

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

theorem GlobalTheory.UnitLemma.PairClass.exists_degreeLT_equiv (F V : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : V →ₗ[F] V) (P : F[X]) (hP : f.charpoly = P) (hs : P.Separable) :
    ∃ (e₀ : V) (ψ : degreeLT F P.natDegree ≃ₗ[F] V), ∀ p, ψ p = aeval f (p : F[X]) e₀ := by sorry
