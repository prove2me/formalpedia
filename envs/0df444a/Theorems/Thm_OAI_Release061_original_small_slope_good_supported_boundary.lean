-- Prove2me | Theorems.Thm_OAI_Release061_original_small_slope_good_supported_boundary
-- name    : OAI.Release061.original_small_slope_good_supported_boundary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:50:04.909644+00:00
-- url     : https://prove2.me/theorems/beae6342-cf8f-4c40-8504-a8c74f967cc3
-- title:
--   OAI.Release061.original_small_slope_good_supported_boundary: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.original_small_slope_good_supported_boundary` of [lean/OAI/Analysis/SymmetricDomains/SmallSlopeGoodSupported.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/SmallSlopeGoodSupported.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology MeasureTheory`, `open scoped Classical`):
--
--   ```lean
--   theorem original_small_slope_good_supported_boundary {n : ℕ} (V U : Set (Affine n))
--       (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
--       (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
--       (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
--       (hs : IsSemialgebraic U)
--       (Γ : Type*) [Group Γ] [MulAction Γ U]
--       [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
--       (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
--       ∃ (m : ℕ) (C : Finset (NashPatch (n+n))),
--         ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
--           ∃ (p : C) (x : Fin p.val.dim → ℝ) (k : ℕ)
--             (F : Affine m → Affine n) (G : Affine n → Affine m)
--             (h : Fin k → Affine n → ℂ),
--             x ∈ p.val.domain ∧ x ∉ bad p ∧ p.val.complexMap x ∈ closure U \ U ∧
--             SmallSlopeGoodNashBoundary m U (MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U))
--               p.val.domain p.val.complexMap x ∧
--             1 ≤ k ∧ k ≤ m ∧ p.val.dim + k = 2*m ∧
--             F 0 = p.val.complexMap x ∧ AnalyticAt ℂ F 0 ∧
--             AnalyticAt ℂ G (p.val.complexMap x) ∧
--             (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id ∧
--             (∀ᶠ y in 𝓝[MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)] (p.val.complexMap x), F (G y) = y) ∧
--             (∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)) ∧
--             Submodule.span ℂ (range (fderiv ℝ (G ∘ p.val.complexMap) x)) = ⊤ ∧
--             (∀ i, AnalyticOnNhd ℂ (h i) univ) ∧
--             (∀ i, h i (p.val.complexMap x) = 1) ∧
--             (∀ i, ∀ z ∈ closure U, ‖h i z‖ ≤ Real.exp (-(dist z (p.val.complexMap x))^2)) ∧
--             (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (F z))) 0) ∧
--             LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap) ∧
--             LinearIndependent ℂ (fun i => (fderiv ℂ (fun z => Complex.log (h i (F z))) 0).toLinearMap) ∧
--             ∀ i, (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).comp (fderiv ℝ (G ∘ p.val.complexMap) x) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.NashPatch`, `OAI.Release061.SmallSlopeGoodNashBoundary` and `OAI.Release061.NashPatch.complexMap` (definitions bundle `OAIQ025S001` of this split); `OAI.Release061.Affine`, `OAI.Release061.HolomorphicOnSubset`, `OAI.Release061.IsAffineAlgebraic` and `OAI.Release061.IsSemialgebraic` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proof of `OAI.Release061.original_supported_hermitian_model` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/SmallSlopeGoodSupported.lean (declaration OAI.Release061.original_small_slope_good_supported_boundary)

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology MeasureTheory
open scoped Classical

theorem original_small_slope_good_supported_boundary {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [MulAction Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (m : ℕ) (C : Finset (NashPatch (n+n))),
      ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
        ∃ (p : C) (x : Fin p.val.dim → ℝ) (k : ℕ)
          (F : Affine m → Affine n) (G : Affine n → Affine m)
          (h : Fin k → Affine n → ℂ),
          x ∈ p.val.domain ∧ x ∉ bad p ∧ p.val.complexMap x ∈ closure U \ U ∧
          SmallSlopeGoodNashBoundary m U (MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U))
            p.val.domain p.val.complexMap x ∧
          1 ≤ k ∧ k ≤ m ∧ p.val.dim + k = 2*m ∧
          F 0 = p.val.complexMap x ∧ AnalyticAt ℂ F 0 ∧
          AnalyticAt ℂ G (p.val.complexMap x) ∧
          (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id ∧
          (∀ᶠ y in 𝓝[MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)] (p.val.complexMap x), F (G y) = y) ∧
          (∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)) ∧
          Submodule.span ℂ (range (fderiv ℝ (G ∘ p.val.complexMap) x)) = ⊤ ∧
          (∀ i, AnalyticOnNhd ℂ (h i) univ) ∧
          (∀ i, h i (p.val.complexMap x) = 1) ∧
          (∀ i, ∀ z ∈ closure U, ‖h i z‖ ≤ Real.exp (-(dist z (p.val.complexMap x))^2)) ∧
          (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (F z))) 0) ∧
          LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap) ∧
          LinearIndependent ℂ (fun i => (fderiv ℂ (fun z => Complex.log (h i (F z))) 0).toLinearMap) ∧
          ∀ i, (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).comp (fderiv ℝ (G ∘ p.val.complexMap) x) = 0 := by
  sorry
end Release061

end

end OAI
end
