-- Prove2me | Theorems.Thm_GlobalTheory_CompleteBaseChange_exists_polynomial_totalDegree_le_sub_mem
-- name    : GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:23.33697+00:00
-- url     : https://prove2.me/theorems/34da2796-7ec5-4881-8715-12a775bad5a7
-- title:
--   Complete Base Change: exists polynomial total Degree le sub mem
-- statement:
--   The Complete Base Change construction uses the exists polynomial total Degree le sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem.lean#L25-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem.lean#L25-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange
open MvPowerSeries

theorem GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem : ∀ (R : Type) [CommRing R] (J : Ideal R), J.FG → IsAdicComplete J R → ∀ (σ ι : Type) [Finite σ] [Finite ι] (f : ι → MvPowerSeries σ R) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) J → ∀ g : MvPowerSeries σ R, ∃ P : MvPolynomial σ R, P.totalDegree ≤ M ∧ g - (P : MvPowerSeries σ R) ∈ Ideal.span (Set.range f) := by sorry
