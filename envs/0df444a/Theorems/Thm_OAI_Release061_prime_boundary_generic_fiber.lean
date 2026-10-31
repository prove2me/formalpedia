-- Prove2me | Theorems.Thm_OAI_Release061_prime_boundary_generic_fiber
-- name    : OAI.Release061.prime_boundary_generic_fiber
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:50:44.583931+00:00
-- url     : https://prove2.me/theorems/b06f2960-597f-4504-9f93-6ea9c772ef50
-- title:
--   OAI.Release061.prime_boundary_generic_fiber: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.prime_boundary_generic_fiber` of [lean/OAI/Analysis/SymmetricDomains/PrimeBoundaryGenericFiber.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/PrimeBoundaryGenericFiber.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology MeasureTheory`, `open scoped Classical`):
--
--   ```lean
--   theorem prime_boundary_generic_fiber {n : ℕ} {U : Set (Affine n)}
--       (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
--       (hI : I = MvPolynomial.vanishingIdeal ℂ U)
--       (hU : IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U))
--       (hc : IsPreconnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
--       (hs : IsSemialgebraic U) :
--       ∃ (m : ℕ) (P : MvPolynomial (Fin n) ℂ) (C : Finset (NashPatch (n+n))),
--         (∃ u ∈ U, MvPolynomial.eval u P ≠ 0) ∧
--         (∀ p ∈ C, 0 ∈ p.domain ∧ ∀ x ∈ p.domain,
--           p.complexMap x ∈ closure U \ U ∧
--           ∃ W : Set (Affine n), W ⊆ MvPolynomial.zeroLocus ℂ I ∧
--             IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' W) ∧ p.complexMap x ∈ W ∧
--             ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B)) ∧
--         ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
--           ∃ p : C, ∃ (c : ActualCriticalChart P p.val.complexMap) (x : Fin p.val.dim → ℝ),
--             x ∈ p.val.domain ∧ x ∈ c.base ∧ m ≤ p.val.complexRank x ∧
--             MvPolynomial.eval (p.val.complexMap x) P ≠ 0 ∧ x ∉ bad p ∧
--             volume (Prod.mk x ⁻¹' c.maxLocus (closure U)) ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.ActualCriticalChart` and `OAI.Release061.ActualCriticalChart.maxLocus` (definitions bundle `OAIQ025S000` of this split); `OAI.Release061.NashPatch`, `OAI.Release061.NashPatch.complexMap` and `OAI.Release061.NashPatch.complexRank` (definitions bundle `OAIQ025S001` of this split); `OAI.Release061.Affine`, `OAI.Release061.Biholomorph` and `OAI.Release061.IsSemialgebraic` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proof of `OAI.Release061.original_small_slope_good_supported_boundary` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/PrimeBoundaryGenericFiber.lean (declaration OAI.Release061.prime_boundary_generic_fiber)

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S000
import Definitions.Def_OAIQ025S001

section

attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
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

theorem prime_boundary_generic_fiber {n : ℕ} {U : Set (Affine n)}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (hI : I = MvPolynomial.vanishingIdeal ℂ U)
    (hU : IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U))
    (hc : IsPreconnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U) :
    ∃ (m : ℕ) (P : MvPolynomial (Fin n) ℂ) (C : Finset (NashPatch (n+n))),
      (∃ u ∈ U, MvPolynomial.eval u P ≠ 0) ∧
      (∀ p ∈ C, 0 ∈ p.domain ∧ ∀ x ∈ p.domain,
        p.complexMap x ∈ closure U \ U ∧
        ∃ W : Set (Affine n), W ⊆ MvPolynomial.zeroLocus ℂ I ∧
          IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' W) ∧ p.complexMap x ∈ W ∧
          ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B)) ∧
      ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
        ∃ p : C, ∃ (c : ActualCriticalChart P p.val.complexMap) (x : Fin p.val.dim → ℝ),
          x ∈ p.val.domain ∧ x ∈ c.base ∧ m ≤ p.val.complexRank x ∧
          MvPolynomial.eval (p.val.complexMap x) P ≠ 0 ∧ x ∉ bad p ∧
          volume (Prod.mk x ⁻¹' c.maxLocus (closure U)) ≠ 0 := by
  sorry

end Release061

end

end OAI
end
