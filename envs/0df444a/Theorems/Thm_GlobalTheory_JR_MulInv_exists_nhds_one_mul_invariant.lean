-- Prove2me | Theorems.Thm_GlobalTheory_JR_MulInv_exists_nhds_one_mul_invariant
-- name    : GlobalTheory.JR.MulInv.exists_nhds_one_mul_invariant
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:34:29.585822+00:00
-- url     : https://prove2.me/theorems/fd17a662-be3c-43f5-9490-98d46c5ac975
-- title:
--   Mul Inv: exists nhds one mul invariant
-- statement:
--   The Mul Inv construction uses the exists nhds one mul invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNhdsOneEtaleAlgebraMulInvariant.lean#L8-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNhdsOneEtaleAlgebraMulInvariant.lean#L8-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsOneEtaleAlgebraMulInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.MulInv

theorem GlobalTheory.JR.MulInv.exists_nhds_one_mul_invariant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ : A.L → ℂ), IsTest φ →
    ∃ U ∈ 𝓝 (1 : A.K), ∀ s ∈ U, ∀ s' ∈ U, s * s' = 1 → ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y := by sorry
