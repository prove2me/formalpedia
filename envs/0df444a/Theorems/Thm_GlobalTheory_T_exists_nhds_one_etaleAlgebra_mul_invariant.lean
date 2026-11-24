-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_nhds_one_etaleAlgebra_mul_invariant
-- name    : GlobalTheory.T.exists_nhds_one_etaleAlgebra_mul_invariant
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:36:44.868801+00:00
-- url     : https://prove2.me/theorems/d1cf7c92-2ed9-415d-a6c7-84415d443df4
-- title:
--   T: exists nhds one etale Algebra mul invariant
-- statement:
--   The T construction uses the exists nhds one etale Algebra mul invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNhdsOneEtaleAlgebraMulInvariantStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNhdsOneEtaleAlgebraMulInvariantStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsOneEtaleAlgebraMulInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsOneEtaleAlgebraMulInvariantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_nhds_one_etaleAlgebra_mul_invariant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ : A.L → ℂ), IsTest φ → ∃ U ∈ 𝓝 (1 : A.K), ∀ s ∈ U, ∀ s' ∈ U, s * s' = 1 → ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y := by sorry
