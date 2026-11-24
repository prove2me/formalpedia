-- Prove2me | Theorems.Thm_GlobalTheory_CompleteBaseChange_monomial_one_mem_span_X_pow
-- name    : GlobalTheory.CompleteBaseChange.monomial_one_mem_span_X_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:08.59136+00:00
-- url     : https://prove2.me/theorems/0ad0fc88-e5a8-486e-91c1-0854e22a1e90
-- title:
--   Complete Base Change: monomial one mem span X pow
-- statement:
--   The Complete Base Change construction uses the monomial one mem span X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem.lean#L10-L23

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

theorem GlobalTheory.CompleteBaseChange.monomial_one_mem_span_X_pow {R σ : Type*} [CommRing R] (α : σ →₀ ℕ) :
    (monomial α (1 : R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ α.degree := by sorry
