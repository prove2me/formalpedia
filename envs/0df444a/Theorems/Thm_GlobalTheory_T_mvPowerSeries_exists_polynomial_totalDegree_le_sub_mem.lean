-- Prove2me | Theorems.Thm_GlobalTheory_T_mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem
-- name    : GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:54:00.024199+00:00
-- url     : https://prove2.me/theorems/87b0c97f-40f2-4a7a-9fad-ea224dd00dfd
-- title:
--   T: mv Power Series exists polynomial total Degree le sub mem
-- statement:
--   The T construction uses the mv Power Series exists polynomial total Degree le sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesExistsPolynomialTotalDegreeLeSubMemStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesExistsPolynomialTotalDegreeLeSubMemStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesExistsPolynomialTotalDegreeLeSubMemStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem : ∀ (R : Type) [CommRing R] (J : Ideal R), J.FG → IsAdicComplete J R → ∀ (σ ι : Type) [Finite σ] [Finite ι] (f : ι → MvPowerSeries σ R) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) J → ∀ g : MvPowerSeries σ R, ∃ P : MvPolynomial σ R, P.totalDegree ≤ M ∧ g - (P : MvPowerSeries σ R) ∈ Ideal.span (Set.range f) := by sorry
