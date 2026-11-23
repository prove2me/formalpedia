-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayData_lseries_eq_exp_tsum
-- name    : GlobalTheory.Mem.RayData.lseries_eq_exp_tsum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:12.646273+00:00
-- url     : https://prove2.me/theorems/b03a3934-482f-4fd3-99f2-637576491352
-- title:
--   Ray Data: lseries eq exp tsum
-- statement:
--   The Ray Data construction uses the lseries eq exp tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayLSeriesEulerProduct.lean#L154-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayLSeriesEulerProduct.lean#L154-L229

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem

theorem GlobalTheory.Mem.RayData.lseries_eq_exp_tsum :
    ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ) (s : ℂ), 1 < s.re → LSeriesSummable (D.coef χ) s ∧ Summable (fun v : D.Pr => ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖) ∧ LSeries (D.coef χ) s = Complex.exp (∑' v : D.Pr, -Complex.log (1 - (χ (D.cls v.1.asIdeal) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by sorry
