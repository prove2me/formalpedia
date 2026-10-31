-- Prove2me | Theorems.Thm_OAI_Release061_original_supported_hermitian_model
-- name    : OAI.Release061.original_supported_hermitian_model
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:52:56.028862+00:00
-- url     : https://prove2.me/theorems/98b37d27-eca1-4664-9859-d6739aae6db9
-- title:
--   OAI.Release061.original_supported_hermitian_model: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.original_supported_hermitian_model` of [lean/OAI/Analysis/SymmetricDomains/SupportedHermitianModel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/SupportedHermitianModel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology Metric MeasureTheory`, `open scoped Classical`):
--
--   ```lean
--   theorem original_supported_hermitian_model {N : ℕ} (V U : Set (Affine N))
--       (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
--       (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
--       (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
--       (hs : IsSemialgebraic U)
--       (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
--       [MulAction Γ U] [ProperSMul Γ U]
--       [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
--       (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
--       ∃ (r k : ℕ) (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ)
--         (C : Set (Fin k → ℝ)) (e : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ)) (c : ℝ),
--         1 ≤ k ∧ IsOpen C ∧ IsConnected C ∧ (0 : Fin k → ℝ) ∉ C ∧
--         (∀ t : ℝ, 0 < t → ∀ y, t • y ∈ C ↔ y ∈ C) ∧ 0 < c ∧
--         (∀ z ∈ quadraticDomain (Hermitian.hermQuadratic B) C,
--           ∀ i, c*‖z.1‖^2 ≤ e (fun j => (z.2 j).im) i) ∧
--         Nonempty (Biholomorph U
--           ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.affineProductCoordinates` (definitions bundle `OAIQ025S000` of this split); `OAI.Release061.Hermitian.hermQuadratic` (definitions bundle `OAIQ025S001` of this split); `OAI.Release061.quadraticDomain` (definitions bundle `OAIQ025S002` of this split); `OAI.Release061.Affine`, `OAI.Release061.Biholomorph`, `OAI.Release061.HolomorphicOnSubset`, `OAI.Release061.IsAffineAlgebraic` and `OAI.Release061.IsSemialgebraic` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proof of `OAI.Release061.main` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/SupportedHermitianModel.lean (declaration OAI.Release061.original_supported_hermitian_model)

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S000
import Definitions.Def_OAIQ025S001
import Definitions.Def_OAIQ025S002

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
open Set Filter Topology Metric MeasureTheory
open scoped Classical

theorem original_supported_hermitian_model {N : ℕ} (V U : Set (Affine N))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (r k : ℕ) (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ)
      (C : Set (Fin k → ℝ)) (e : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ)) (c : ℝ),
      1 ≤ k ∧ IsOpen C ∧ IsConnected C ∧ (0 : Fin k → ℝ) ∉ C ∧
      (∀ t : ℝ, 0 < t → ∀ y, t • y ∈ C ↔ y ∈ C) ∧ 0 < c ∧
      (∀ z ∈ quadraticDomain (Hermitian.hermQuadratic B) C,
        ∀ i, c*‖z.1‖^2 ≤ e (fun j => (z.2 j).im) i) ∧
      Nonempty (Biholomorph U
        ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C)) := by
  sorry

end Release061

end

end OAI
end
