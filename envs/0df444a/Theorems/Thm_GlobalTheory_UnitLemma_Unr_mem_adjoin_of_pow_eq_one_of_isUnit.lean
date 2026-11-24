-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_mem_adjoin_of_pow_eq_one_of_isUnit
-- name    : GlobalTheory.UnitLemma.Unr.mem_adjoin_of_pow_eq_one_of_isUnit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:38:18.751001+00:00
-- url     : https://prove2.me/theorems/0f9b6608-06b8-40e0-9dd3-042ef0cec8f6
-- title:
--   Unr: mem adjoin of pow eq one of is Unit
-- statement:
--   The Unr construction uses the mem adjoin of pow eq one of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic.lean#L8-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic.lean#L8-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open Polynomial

theorem GlobalTheory.UnitLemma.Unr.mem_adjoin_of_pow_eq_one_of_isUnit {R F L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {z : L} {N : ℕ} (hN : IsUnit (N : R)) (hz : z ^ N = 1) (hadj : Algebra.adjoin F {z} = ⊤)
    {y : L} (hy : IsIntegral R y) : y ∈ Algebra.adjoin R {z} := by sorry
