-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_fine_global_scalar_tensor_approximation
-- name    : OAI.ScalarConductivity.fine_global_scalar_tensor_approximation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:45:53.622991+00:00
-- url     : https://prove2.me/theorems/666bd34f-045e-436e-a177-c3fc41472425
-- title:
--   OAI.ScalarConductivity.fine_global_scalar_tensor_approximation: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.fine_global_scalar_tensor_approximation` of [lean/OAI/Analysis/Conductivity/Geometry/RegularRegionCongrSubset.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Geometry/RegularRegionCongrSubset.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open MeasureTheory`, `open scoped ENNReal`, `open Matrix Filter Topology`, `open Set MeasureTheory Filter Topology`, `open scoped BigOperators`, `open Set MeasureTheory Filter Topology`, `open scoped Manifold`, `open Set Filter`, `open scoped Topology`, `open Set Filter MeasureTheory`, `open scoped Topology Manifold ENNReal`, `open Set`, `open Matrix Set MeasureTheory Filter Topology`, `open scoped Matrix.Norms.Elementwise ENNReal`):
--
--   ```lean
--   theorem fine_global_scalar_tensor_approximation
--       (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
--       {a b : ℝ} (ha : 0 < a) (hab : a < b)
--       {U : Set Coord3} (hUb : Bornology.IsBounded U)
--       (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
--       (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
--       (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
--         tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
--       (hreg : μ (U \ regularRegion u A U) = 0)
--       (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b)
--       {η ε δ : ℝ} (hη : 0 < η) (hε : 0 < ε) (hδ : 0 < δ) :
--       ∃ (N : ℕ) (O : Fin N → Set Coord3) (center : Fin N → Coord3)
--         (R : ∀ i, CompactGlobalUpdate μ (O i) u A) (S : CompactGlobalUpdate μ U u A),
--         (∀ i, IsOpen (O i) ∧ closure (O i) ⊆ U ∧ closure (O i) ⊆ Metric.ball (center i) δ) ∧
--         Pairwise (fun i j => Disjoint (O i) (O j)) ∧
--         S.du = (fun x => ∑ i, (R i).du x) ∧ S.dF = (fun x => ∑ i, (R i).dF x) ∧
--         μ (U \ regularRegion (fun x => u x+S.du x) S.tensor U) = 0 ∧
--         (∀ᵐ x ∂μ, x ∈ U → S.tensor x ∈ matrixFiniteLaminate a b) ∧
--         μ (U \ S.tensor ⁻¹' spectralExtension (scalarNeighbourhood a b η)) ≤ ENNReal.ofReal ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.Symmetric3` and `OAI.ScalarConductivity.regularRegion` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.CompactGlobalUpdate`, `OAI.ScalarConductivity.conductivityFlux` and `OAI.ScalarConductivity.instMeasurableSpaceSymmetric3` (definitions bundle `OAIQ059C003` of this split); `OAI.ScalarConductivity.SmoothFluxIntegrable` (definitions bundle `OAIQ059C004` of this split); `OAI.ScalarConductivity.matrixFiniteLaminate`, `OAI.ScalarConductivity.scalarNeighbourhood` and `OAI.ScalarConductivity.spectralExtension` (definitions bundle `OAIQ059C005` of this split).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.finite_field_scalarization` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Geometry/RegularRegionCongrSubset.lean (declaration OAI.ScalarConductivity.fine_global_scalar_tensor_approximation)

import Mathlib
import Definitions.Def_OAIQ059C003
import Definitions.Def_OAIQ059C004
import Definitions.Def_OAIQ059C005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

theorem fine_global_scalar_tensor_approximation
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b)
    {η ε δ : ℝ} (hη : 0 < η) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (N : ℕ) (O : Fin N → Set Coord3) (center : Fin N → Coord3)
      (R : ∀ i, CompactGlobalUpdate μ (O i) u A) (S : CompactGlobalUpdate μ U u A),
      (∀ i, IsOpen (O i) ∧ closure (O i) ⊆ U ∧ closure (O i) ⊆ Metric.ball (center i) δ) ∧
      Pairwise (fun i j => Disjoint (O i) (O j)) ∧
      S.du = (fun x => ∑ i, (R i).du x) ∧ S.dF = (fun x => ∑ i, (R i).dF x) ∧
      μ (U \ regularRegion (fun x => u x+S.du x) S.tensor U) = 0 ∧
      (∀ᵐ x ∂μ, x ∈ U → S.tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (U \ S.tensor ⁻¹' spectralExtension (scalarNeighbourhood a b η)) ≤ ENNReal.ofReal ε := by
  sorry

end ScalarConductivity

end

end OAI
end
