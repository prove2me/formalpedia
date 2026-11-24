-- Prove2me | Theorems.Thm_GlobalTheory_Mem_lseriesSummable_card_absNorm
-- name    : GlobalTheory.Mem.lseriesSummable_card_absNorm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:24:55.137033+00:00
-- url     : https://prove2.me/theorems/b15ce41b-0ee8-40fd-950a-0881c0372290
-- title:
--   Mem: lseries Summable card abs Norm
-- statement:
--   The Mem construction uses the lseries Summable card abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayLSeriesEulerProduct.lean#L89-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayLSeriesEulerProduct.lean#L89-L108

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

theorem GlobalTheory.Mem.lseriesSummable_card_absNorm (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) s := by sorry
