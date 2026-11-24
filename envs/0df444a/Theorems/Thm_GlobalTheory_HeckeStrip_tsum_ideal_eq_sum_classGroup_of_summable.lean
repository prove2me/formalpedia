-- Prove2me | Theorems.Thm_GlobalTheory_HeckeStrip_tsum_ideal_eq_sum_classGroup_of_summable
-- name    : GlobalTheory.HeckeStrip.tsum_ideal_eq_sum_classGroup_of_summable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:51.586966+00:00
-- url     : https://prove2.me/theorems/94455dce-85b1-47f5-9c30-e10be4b8a670
-- title:
--   Hecke Strip: tsum ideal eq sum class Group of summable
-- statement:
--   The Hecke Strip construction uses the tsum ideal eq sum class Group of summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeLSeriesEqSumPrincipalPartialSeries.lean#L17-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeLSeriesEqSumPrincipalPartialSeries.lean#L17-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeStrip
open Classical

theorem GlobalTheory.HeckeStrip.tsum_ideal_eq_sum_classGroup_of_summable {K : Type} [Field K] [NumberField K]
    (b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰) (G : Ideal (𝓞 K) → ℂ) (H : ClassGroup (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hb : Function.Bijective (fun c => ClassGroup.mk0 (b c))) (h0 : G ⊥ = 0) (hsum : Summable G)
    (hH : ∀ c I, I ≠ ⊥ → H c (I * b c) = G I) :
    ∑' I, G I = ∑ c, ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ (b c : Ideal (𝓞 K))}, H c J := by sorry
