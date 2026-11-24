-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayData_coef_eq_tsum
-- name    : GlobalTheory.Mem.RayData.coef_eq_tsum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:55.742061+00:00
-- url     : https://prove2.me/theorems/8a350734-2a8c-485d-85f8-6a91960687f5
-- title:
--   Ray Data: coef eq tsum
-- statement:
--   The Ray Data construction uses the coef eq tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayLSeriesEulerProduct.lean#L133-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayLSeriesEulerProduct.lean#L133-L152

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
open Classical

theorem GlobalTheory.Mem.RayData.coef_eq_tsum {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
    (χ : D.G →* ℂˣ) (n : ℕ) :
    D.coef χ n = ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      if IsCoprime I.1 (Ideal.span {(M : 𝓞 K)}) then (χ (D.cls I.1) : ℂ) else 0 := by sorry
